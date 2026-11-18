/-
Copyright (c) 2026 David Gupta (Nico). Released under the MIT license (see LICENSE).
Written with AI assistance as a UW Math AI Lab project.

# Generation 1: conservative replication is refuted

After one generation in ¹⁴N, Meselson and Stahl saw a single band at
50 ± 2% of the way from light to heavy. In our encoding that is the
observation `{1/2}`.
-/
import MeselsonStahl.Basic

namespace MeselsonStahl

open Klavins Model

/-- The actual generation-1 observation: one hybrid band at 1/2. -/
def obs1 : Obs := {1/2}

/-- The observation `{1/2}` is allowed by the semiconservative model
(whenever `ε ≥ 0`). -/
theorem obs1_mem_semi {ε : ℚ} (hε : 0 ≤ ε) : obs1 ∈ E1 ε Semiconservative :=
  -- `{1/2}` is exactly the semiconservative ideal, so `matches_self` applies
  matches_self hε _

/-- … and also by the dispersive model. -/
theorem obs1_mem_disp {ε : ℚ} (hε : 0 ≤ ε) : obs1 ∈ E1 ε UniformDispersive :=
  matches_self hε _

/-- In generation 1, conservative outcomes never overlap semiconservative
ones, as long as `ε < 1/4`. -/
theorem E1_disjoint_cons_semi {ε : ℚ} (hε : ε < 1/4) :
    Disjoint (E1 ε Conservative) (E1 ε Semiconservative) := by
  -- the conservative band `1` is far from the only semiconservative band `1/2`
  refine disjoint_of_far 1 (by simp [ideal1]) ?_
  intro d hd
  simp [ideal1] at hd  -- `hd : d = 1/2`
  subst hd
  norm_num  -- goal: `2 * ε < |1 - 1/2|`, i.e. `2 * ε < 1/2`
  linarith

/-- … and the same for conservative vs. dispersive. -/
theorem E1_disjoint_cons_disp {ε : ℚ} (hε : ε < 1/4) :
    Disjoint (E1 ε Conservative) (E1 ε UniformDispersive) := by
  refine disjoint_of_far 1 (by simp [ideal1]) ?_
  intro d hd
  simp [ideal1] at hd
  subst hd
  norm_num
  linarith

/-- **Theorem 1.** The generation-1 observation `{1/2}` refutes the
hypothesis "replication is conservative" (for `0 ≤ ε < 1/4`, which covers the
reported ε = 2%). -/
theorem gen1_refutes_conservative {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/4) :
    refutes (E1 ε) {Conservative} obs1 := by
  -- `{1/2}` is a semiconservative outcome, and no conservative outcome is
  -- also a semiconservative outcome
  apply refutes_of_mem_of_disjoint (obs1_mem_semi h0)
  intro m hm
  simp at hm  -- `hm : m = Conservative`
  subst hm
  exact E1_disjoint_cons_semi hε

/-- The concrete instance with the reported ±2% error. -/
theorem gen1_refutes_conservative_2pct :
    refutes (E1 (1/50)) {Conservative} obs1 :=
  gen1_refutes_conservative (by norm_num) (by norm_num)

/-- Bonus: generation 1 *discriminates* the conservative hypothesis from the
other two, so it was informative about it. -/
theorem gen1_discriminates_conservative {ε : ℚ} (hε : ε < 1/4) :
    discriminates (E1 ε) {Conservative} := by
  intro m1 hm1 m2 hm2
  simp at hm1 hm2  -- `hm1 : m1 = Conservative`, `hm2 : m2 ≠ Conservative`
  subst hm1
  cases m2 with
  | Conservative => exact absurd rfl hm2
  | Semiconservative => exact E1_disjoint_cons_semi hε
  | UniformDispersive => exact E1_disjoint_cons_disp hε

/-- Generation 1 is informative about the conservative hypothesis. -/
theorem gen1_informative_conservative {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/4) :
    informative (E1 ε) {Conservative} :=
  discriminates_implies_informative (gen1_discriminates_conservative hε)
    ⟨Semiconservative, by simp, obs1, obs1_mem_semi h0⟩

/-- **Theorem 2.** Generation 1 does *not* discriminate semiconservative from
dispersive replication: the outcome `{1/2}` is allowed by both. (True for
every `ε ≥ 0`, no matter how precise the measurement.) -/
theorem gen1_not_discriminates_semi {ε : ℚ} (h0 : 0 ≤ ε) :
    ¬ discriminates (E1 ε) {Semiconservative} := by
  -- by `not_discriminates`, it is enough to find an overlapping pair
  rw [not_discriminates]
  refine ⟨Semiconservative, by simp, UniformDispersive, by simp, ?_⟩
  -- `{1/2}` lies in both outcome sets, so they are not disjoint
  exact Set.not_disjoint_iff.mpr ⟨obs1, obs1_mem_semi h0, obs1_mem_disp h0⟩

/-- In fact the two models allow *exactly* the same generation-1 outcomes,
because they predict the same ideal bands. -/
theorem gen1_semi_eq_disp (ε : ℚ) :
    E1 ε Semiconservative = E1 ε UniformDispersive := rfl

end MeselsonStahl
