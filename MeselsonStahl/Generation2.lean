/-
Copyright (c) 2026 David Gupta (Nico). Released under the MIT license (see LICENSE).
Written with AI assistance as a UW Math AI Lab project.

# Generation 2: only semiconservative replication survives

After two generations in ¹⁴N, Meselson and Stahl saw a hybrid band and a light
band in equal amounts. In our encoding that is the observation `{0, 1/2}`.

The key fact is that, with measurement error `ε < 1/8`, the three models'
generation-2 outcome sets are pairwise disjoint: the closest pair of ideal
bands from different models is `0` vs `1/4` (or `1/4` vs `1/2`), which are
`1/4 > 2ε` apart.
-/
import MeselsonStahl.Basic

namespace MeselsonStahl

open Klavins Model

/-! ## Pairwise disjointness -/

/-- Conservative vs. semiconservative: the conservative band `1` is at
distance `1` from `0` and `1/2` from `1/2`, both more than `2ε`. -/
theorem E2_disjoint_cons_semi {ε : ℚ} (hε : ε < 1/8) :
    Disjoint (E2 ε Conservative) (E2 ε Semiconservative) := by
  refine disjoint_of_far 1 (by simp [ideal2]) ?_
  intro d hd
  -- `hd : d = 0 ∨ d = 1/2`; check each case
  simp only [ideal2, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> norm_num <;> linarith

/-- Conservative vs. dispersive: the dispersive band `1/4` is at distance
`1/4` from `0` and `3/4` from `1`. (We prove it in the order dispersive,
conservative and then flip it with `.symm`.) -/
theorem E2_disjoint_cons_disp {ε : ℚ} (hε : ε < 1/8) :
    Disjoint (E2 ε Conservative) (E2 ε UniformDispersive) := by
  refine Disjoint.symm (disjoint_of_far (1/4) (by simp [ideal2]) ?_)
  intro d hd
  simp only [ideal2, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> norm_num <;> linarith

/-- Semiconservative vs. dispersive: the dispersive band `1/4` is at distance
`1/4` from both `0` and `1/2`. -/
theorem E2_disjoint_semi_disp {ε : ℚ} (hε : ε < 1/8) :
    Disjoint (E2 ε Semiconservative) (E2 ε UniformDispersive) := by
  refine Disjoint.symm (disjoint_of_far (1/4) (by simp [ideal2]) ?_)
  intro d hd
  simp only [ideal2, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> norm_num <;> linarith

/-- **Theorem 3.** In generation 2, any two *different* models have disjoint
outcome sets (when `ε < 1/8`). -/
theorem E2_pairwise_disjoint {ε : ℚ} (hε : ε < 1/8) :
    ∀ m1 m2 : Model, m1 ≠ m2 → Disjoint (E2 ε m1) (E2 ε m2) := by
  -- go through all 3 × 3 = 9 pairs of models
  intro m1 m2 hne
  cases m1 <;> cases m2
  -- the 3 pairs with `m1 = m2` contradict `hne`
  all_goals first
    | exact absurd rfl hne
    -- the other 6 are our three lemmas, possibly flipped
    | exact E2_disjoint_cons_semi hε
    | exact (E2_disjoint_cons_semi hε).symm
    | exact E2_disjoint_cons_disp hε
    | exact (E2_disjoint_cons_disp hε).symm
    | exact E2_disjoint_semi_disp hε
    | exact (E2_disjoint_semi_disp hε).symm

/-- Generation 2 discriminates **every** hypothesis (when `ε < 1/8`). -/
theorem gen2_discriminates {ε : ℚ} (hε : ε < 1/8) (H : Hypothesis MS) :
    discriminates (E2 ε) H :=
  discriminates_of_pairwise_disjoint (E2_pairwise_disjoint hε)

/-- In particular each single model is discriminated from the other two. -/
theorem gen2_discriminates_conservative {ε : ℚ} (hε : ε < 1/8) :
    discriminates (E2 ε) {Conservative} := gen2_discriminates hε _

theorem gen2_discriminates_semi {ε : ℚ} (hε : ε < 1/8) :
    discriminates (E2 ε) {Semiconservative} := gen2_discriminates hε _

theorem gen2_discriminates_disp {ε : ℚ} (hε : ε < 1/8) :
    discriminates (E2 ε) {UniformDispersive} := gen2_discriminates hε _

/-! ## The actual generation-2 observation -/

/-- The actual generation-2 observation: a light band (0) and a hybrid
band (1/2). -/
def obs2 : Obs := {0, 1/2}

/-- `{0, 1/2}` is a semiconservative outcome (whenever `ε ≥ 0`). -/
theorem obs2_mem_semi {ε : ℚ} (hε : 0 ≤ ε) : obs2 ∈ E2 ε Semiconservative :=
  matches_self hε _

/-- **Theorem 4.** The generation-2 observation `{0, 1/2}` refutes the
hypothesis "conservative or dispersive" (for `0 ≤ ε < 1/8`). -/
theorem gen2_refutes_cons_disp {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/8) :
    refutes (E2 ε) {Conservative, UniformDispersive} obs2 := by
  -- `obs2` is semiconservative, and semiconservative outcomes never overlap
  -- conservative or dispersive outcomes
  apply refutes_of_mem_of_disjoint (obs2_mem_semi h0)
  intro m hm
  exact E2_pairwise_disjoint hε m Semiconservative (by
    -- `m` is conservative or dispersive, so it is not semiconservative
    rcases hm with rfl | rfl <;> simp)

/-- Theorem 4, both halves together. -/
theorem gen2_result {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/8) :
    refutes (E2 ε) {Conservative, UniformDispersive} obs2 ∧
      obs2 ∈ E2 ε Semiconservative :=
  ⟨gen2_refutes_cons_disp h0 hε, obs2_mem_semi h0⟩

/-- The concrete instance with the reported ±2% error. -/
theorem gen2_result_2pct :
    refutes (E2 (1/50)) {Conservative, UniformDispersive} obs2 ∧
      obs2 ∈ E2 (1/50) Semiconservative :=
  gen2_result (by norm_num) (by norm_num)

/-- Generation 2 is informative about "conservative or dispersive". -/
theorem gen2_informative_cons_disp {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/8) :
    informative (E2 ε) {Conservative, UniformDispersive} :=
  discriminates_implies_informative (gen2_discriminates hε _)
    ⟨Semiconservative, by simp, obs2, obs2_mem_semi h0⟩

/-- Why we need `ε < 1/8`: the bound is sharp. With `ε = 1/8` exactly, the
observation `{1/8, 3/8}` is allowed by *both* the semiconservative model
(`1/8` is near `0`, `3/8` is near `1/2`) and the dispersive model (both bands
are within `1/8` of `1/4`). -/
theorem gen2_not_disjoint_at_eighth :
    ¬ Disjoint (E2 (1/8) Semiconservative) (E2 (1/8) UniformDispersive) := by
  rw [Set.not_disjoint_iff]
  refine ⟨{1/8, 3/8}, ?_, ?_⟩ <;>
    simp only [E2, bandExperiment, Set.mem_ofPred_eq, Matches, ideal2,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      exists_eq_or_imp, exists_eq_left] <;> norm_num [abs_le]

end MeselsonStahl
