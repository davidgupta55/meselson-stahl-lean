/-
Copyright (c) 2026 David Gupta (Nico). Released under the MIT license (see LICENSE).
Written with AI assistance as a UW Math AI Lab project.

# Meselson–Stahl (1958): models and experiments

M. Meselson and F. W. Stahl, "The Replication of DNA in Escherichia coli",
PNAS 44(7):671–682, 1958. https://www.pnas.org/doi/10.1073/pnas.44.7.671

The experiment: E. coli are grown on heavy nitrogen (¹⁵N) and then switched to
light nitrogen (¹⁴N). After each generation the DNA is spun in a cesium
chloride density gradient and forms bands. We record the position of each band
on a scale from `0` (fully light, ¹⁴N DNA) to `1` (fully heavy, ¹⁵N DNA).

This file sets up:
* the three candidate models of replication,
* the *ideal* band positions each model predicts after generations 1 and 2,
* the experiments `E1 ε` and `E2 ε`, which allow any observation that matches
  the ideal bands up to a measurement error `ε`.
-/
import MeselsonStahl.Framework

namespace MeselsonStahl

open Klavins

/-! ## Models -/

/-- The three hypotheses about how DNA copies itself. -/
inductive Model where
  /-- The parent double helix stays together; the copy is entirely new. -/
  | Conservative
  /-- Each copy keeps one old strand and gets one new strand. -/
  | Semiconservative
  /-- Old and new material is mixed evenly through both copies. -/
  | UniformDispersive
  deriving DecidableEq

open Model

/-! ## Observations and the setting -/

/-- An observation is the finite set of band positions we see in the
centrifuge tube, on the 0 (light) … 1 (heavy) scale. -/
abbrev Obs : Type := Finset ℚ

/-- The Meselson–Stahl setting for Klavins's framework. (An `abbrev`, so Lean
knows `MS.Model` is just `Model` and `MS.Obs` is just `Obs`.) -/
abbrev MS : Setting := ⟨Model, Obs⟩

/-! ## Ideal bands predicted by each model -/

/-- Ideal band positions after **one** generation in ¹⁴N.
* conservative: the old heavy molecule (1) and a new light one (0);
* semiconservative: every molecule is half old, half new (1/2);
* dispersive: every molecule is evenly half old, half new (1/2). -/
def ideal1 : Model → Finset ℚ
  | Conservative => {0, 1}
  | Semiconservative => {1/2}
  | UniformDispersive => {1/2}

/-- Ideal band positions after **two** generations in ¹⁴N.
* conservative: still heavy (1) and light (0) molecules, in ratio 1 : 3;
* semiconservative: hybrid (1/2) and light (0) molecules, in ratio 1 : 1;
* dispersive: every molecule is one quarter old (1/4). -/
def ideal2 : Model → Finset ℚ
  | Conservative => {0, 1}
  | Semiconservative => {0, 1/2}
  | UniformDispersive => {1/4}

/-! ## Matching up to measurement error

**Modeling assumption (bounded error).** We assume every measured band lies
within `ε` of a true band position, and every true band is seen within `ε`.
The paper reports the generation-1 band at "50 ± 2%" of the way from light to
heavy; that ±2% is a *statistical* error, not a guaranteed hard bound. So
treating it as a hard bound `ε` is a modeling assumption that we make
explicit: every theorem below says exactly which `ε` it needs. Our concrete
instance is `ε = 1/50` (2%), and the general theorems need `0 ≤ ε < 1/8`.
-/

/-- The observed bands `o` match the ideal bands `I` up to error `ε`:
every observed band is close to some ideal band, and every ideal band is
close to some observed band. -/
def Matches (ε : ℚ) (I o : Finset ℚ) : Prop :=
  (∀ b ∈ o, ∃ c ∈ I, |b - c| ≤ ε) ∧ (∀ c ∈ I, ∃ b ∈ o, |b - c| ≤ ε)

/-- Build an experiment from a table of ideal bands: model `m` allows exactly
the observations that match its ideal bands up to `ε`. -/
def bandExperiment (ideal : Model → Finset ℚ) (ε : ℚ) : Experiment MS :=
  fun m => {o | Matches ε (ideal m) o}

/-- The generation-1 experiment with error `ε`. -/
def E1 (ε : ℚ) : Experiment MS := bandExperiment ideal1 ε

/-- The generation-2 experiment with error `ε`. -/
def E2 (ε : ℚ) : Experiment MS := bandExperiment ideal2 ε

/-! ## Two helper lemmas -/

/-- With error `ε ≥ 0`, seeing *exactly* the ideal bands is always allowed. -/
theorem matches_self {ε : ℚ} (hε : 0 ≤ ε) (I : Finset ℚ) : Matches ε I I := by
  -- each band is within `ε` of itself, since `|b - b| = 0 ≤ ε`
  constructor <;> intro b hb <;> exact ⟨b, hb, by simpa using hε⟩

/-- **The key separation lemma.** Suppose some ideal band `c` of `I` is
more than `2ε` away from every ideal band of `J`. Then no observation can
match both `I` and `J`.

Why: the observation must contain a band `b` within `ε` of `c` (to cover `c`
for `I`), and that same `b` must be within `ε` of some `d ∈ J` (to match `J`).
Then `c` and `d` would be within `2ε` of each other — contradiction. -/
theorem not_matches_both {ε : ℚ} {I J : Finset ℚ} (c : ℚ) (hc : c ∈ I)
    (hfar : ∀ d ∈ J, 2 * ε < |c - d|) (o : Finset ℚ) :
    Matches ε I o → ¬ Matches ε J o := by
  rintro ⟨-, hcover⟩ ⟨hclose, -⟩
  -- a band `b` in `o` near `c` …
  obtain ⟨b, hb, hbc⟩ := hcover c hc
  -- … is also near some `d` in `J`
  obtain ⟨d, hd, hbd⟩ := hclose b hb
  have h := hfar d hd
  -- unfold the absolute values into pairs of inequalities and add them up
  rw [abs_le] at hbc hbd
  rw [lt_abs] at h
  rcases h with h | h <;> linarith [hbc.1, hbc.2, hbd.1, hbd.2]

/-- The separation lemma, phrased as disjointness of the experiment's
outcome sets for two models. -/
theorem disjoint_of_far {ideal : Model → Finset ℚ} {ε : ℚ} {m1 m2 : Model}
    (c : ℚ) (hc : c ∈ ideal m1) (hfar : ∀ d ∈ ideal m2, 2 * ε < |c - d|) :
    Disjoint (bandExperiment ideal ε m1) (bandExperiment ideal ε m2) :=
  Set.disjoint_left.mpr fun o h1 h2 => not_matches_both c hc hfar o h1 h2

end MeselsonStahl
