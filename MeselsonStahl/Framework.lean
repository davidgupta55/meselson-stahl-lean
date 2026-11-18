/-
Copyright (c) 2026 David Gupta (Nico). Released under the MIT license (see LICENSE).
Written with AI assistance as a UW Math AI Lab project.

# A small framework for the scientific method

This file RECREATES Prof. Eric Klavins's "scientific method" framework from
the definitions relayed to us (the original code is not public, so this is a
faithful re-implementation, not a copy). The names and shapes follow his:

* a `Setting` says what the possible *models* of the world are and what the
  possible *observations* are;
* an `Experiment` says, for each model, which observations it allows;
* a `Hypothesis` is a set of models (the models we think might be right);
* an observation `o` *refutes* `H` if no model in `H` allows `o`;
* `E` is *informative* about `H` if some possible outcome refutes `H`;
* `E` *discriminates* `H` if no model inside `H` and model outside `H` can
  ever produce the same observation.

The lemmas at the end (`not_refutes`, `not_discriminates`, `discriminates_iff`,
`discriminates_implies_informative`, ...) are the general facts we use in
`MeselsonStahl/Basic.lean`.
-/
import Mathlib

namespace Klavins

/-- A setting: the possible models of the world and the possible observations. -/
structure Setting where
  /-- The candidate explanations (here: ways DNA might replicate). -/
  Model : Type
  /-- The things we can see in the lab (here: band positions). -/
  Obs : Type

variable {S : Setting}

/-- An experiment assigns to each model the set of observations it allows. -/
abbrev Experiment (S : Setting) : Type := S.Model → Set S.Obs

/-- A hypothesis is a set of models. (We use `abbrev` rather than `def` so Lean
sees through the name and lets us use set notation like `m ∈ H` and `Hᶜ`.) -/
abbrev Hypothesis (S : Setting) : Type := Set S.Model

/-- The observation `o` refutes `H`: no model in `H` allows `o`. -/
def refutes (E : Experiment S) (H : Hypothesis S) (o : S.Obs) : Prop :=
  ∀ m ∈ H, o ∉ E m

/-- `E` is informative about `H`: some model can produce an outcome that refutes `H`. -/
def informative (E : Experiment S) (H : Hypothesis S) : Prop :=
  ∃ m, ∃ o ∈ E m, refutes E H o

/-- `E` discriminates `H`: models inside and outside `H` never share an outcome. -/
def discriminates (E : Experiment S) (H : Hypothesis S) : Prop :=
  ∀ m1 ∈ H, ∀ m2 ∉ H, Disjoint (E m1) (E m2)

variable {E : Experiment S} {H : Hypothesis S} {o : S.Obs}

/-- `o` fails to refute `H` exactly when some model in `H` allows `o`. -/
theorem not_refutes : ¬ refutes E H o ↔ ∃ m ∈ H, o ∈ E m := by
  -- unfold the definition, then push the `¬` inside the `∀` (it becomes `∃`)
  simp [refutes]

/-- `E` fails to discriminate `H` exactly when some inside/outside pair overlaps. -/
theorem not_discriminates :
    ¬ discriminates E H ↔ ∃ m1 ∈ H, ∃ m2 ∉ H, ¬ Disjoint (E m1) (E m2) := by
  simp [discriminates]

/-- Elementwise form: every outcome of an inside model is impossible for every
outside model. -/
theorem discriminates_iff :
    discriminates E H ↔ ∀ m1 ∈ H, ∀ m2 ∉ H, ∀ o, o ∈ E m1 → o ∉ E m2 := by
  -- `Set.disjoint_left` turns `Disjoint A B` into `∀ a ∈ A, a ∉ B`
  simp only [discriminates, Set.disjoint_left]

/-- If `o` is allowed by a model `m'` whose outcomes never overlap those of any
model in `H`, then `o` refutes `H`. -/
theorem refutes_of_mem_of_disjoint {m' : S.Model} (ho : o ∈ E m')
    (hdisj : ∀ m ∈ H, Disjoint (E m) (E m')) : refutes E H o := by
  intro m hm hoE
  -- `o` would be in both `E m` and `E m'`, which are disjoint
  exact Set.disjoint_left.mp (hdisj m hm) hoE ho

/-- Discrimination is symmetric: discriminating `H` is the same as
discriminating its complement. -/
theorem discriminates_compl (h : discriminates E H) : discriminates E Hᶜ := by
  intro m1 hm1 m2 hm2
  -- `m2 ∉ Hᶜ` means `m2 ∈ H`; then use `h` and flip the disjointness
  exact (h m2 (not_not.mp hm2) m1 hm1).symm

/-- **Discriminating implies informative**, under the minimal extra assumption
that some model *outside* `H` can actually produce an outcome. That outcome
then refutes `H`. (We need a model outside `H`: an outcome of a model inside
`H` can never refute `H`.) -/
theorem discriminates_implies_informative (h : discriminates E H)
    (hne : ∃ m ∉ H, (E m).Nonempty) : informative E H := by
  obtain ⟨m2, hm2, o, ho⟩ := hne
  -- the witness is the outside model `m2` and its outcome `o`
  exact ⟨m2, o, ho, refutes_of_mem_of_disjoint ho fun m1 hm1 => h m1 hm1 m2 hm2⟩

/-- The mirror image: if some model *inside* `H` can produce an outcome, then a
discriminating experiment is informative about the complement `Hᶜ`. -/
theorem discriminates_implies_informative_compl (h : discriminates E H)
    (hne : ∃ m ∈ H, (E m).Nonempty) : informative E Hᶜ :=
  discriminates_implies_informative (discriminates_compl h)
    (by obtain ⟨m, hm, hE⟩ := hne; exact ⟨m, not_not.mpr hm, hE⟩)

/-- If the outcome sets of different models never overlap, the experiment
discriminates every hypothesis. -/
theorem discriminates_of_pairwise_disjoint
    (h : ∀ m1 m2 : S.Model, m1 ≠ m2 → Disjoint (E m1) (E m2)) :
    discriminates E H := by
  intro m1 hm1 m2 hm2
  -- `m1 ∈ H` and `m2 ∉ H`, so they are different models
  exact h m1 m2 (by rintro rfl; exact hm2 hm1)

end Klavins
