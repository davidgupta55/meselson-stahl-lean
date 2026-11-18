# Notes: how Meselson–Stahl became Lean

These notes are for someone who knows Lean basics and some set theory. They
explain *why* each definition looks the way it does and walk through every
proof step by step.

## 0. The big picture

The paper is a textbook example of a **crucial experiment**: three rival
models make different predictions, and the data rule out all but one. Prof.
Klavins's framework gives precise names to the pieces:

| Idea | Lean name | Meaning |
|---|---|---|
| What could be true | `S.Model` | the three replication models |
| What we can see | `S.Obs` | the set of band positions in the tube |
| An experiment | `E : Experiment S` | for each model `m`, the set `E m` of outcomes it allows |
| A hypothesis | `H : Hypothesis S` | a set of models, e.g. `{Conservative}` |
| Refutation | `refutes E H o` | no model in `H` allows outcome `o` |
| Informative | `informative E H` | some possible outcome would refute `H` |
| Discriminates | `discriminates E H` | models in `H` and models outside `H` never share an outcome |

The framework code isn't public, so `MeselsonStahl/Framework.lean` **re-creates**
it from the definitions that were relayed to us. A comment at the top of the
file says so.

## 1. Framework.lean

### Definitions

```lean
structure Setting where
  Model : Type
  Obs : Type

abbrev Experiment (S : Setting) : Type := S.Model → Set S.Obs
abbrev Hypothesis (S : Setting) : Type := Set S.Model

def refutes (E : Experiment S) (H : Hypothesis S) (o : S.Obs) : Prop :=
  ∀ m ∈ H, o ∉ E m
def informative (E : Experiment S) (H : Hypothesis S) : Prop :=
  ∃ m, ∃ o ∈ E m, refutes E H o
def discriminates (E : Experiment S) (H : Hypothesis S) : Prop :=
  ∀ m1 ∈ H, ∀ m2 ∉ H, Disjoint (E m1) (E m2)
```

**Why `abbrev` and not `def`?** With `def Hypothesis ...`, Lean treats
`Hypothesis S` as a brand-new type and forgets that it is a `Set`, so `m ∈ H`
and `Hᶜ` stopped working ("failed to synthesize Membership"). `abbrev` tells
Lean "this is just a nickname", so all the set notation works.

### General lemmas

* `not_refutes : ¬ refutes E H o ↔ ∃ m ∈ H, o ∈ E m`. Proof: `simp [refutes]`.
  `simp` unfolds the definition and pushes `¬` through `∀` (it turns into `∃`)
  and through `∉` (a double negation, which cancels).
* `not_discriminates : ¬ discriminates E H ↔ ∃ m1 ∈ H, ∃ m2 ∉ H, ¬ Disjoint (E m1) (E m2)`.
  Same idea, `simp [discriminates]`.
* `discriminates_iff : discriminates E H ↔ ∀ m1 ∈ H, ∀ m2 ∉ H, ∀ o, o ∈ E m1 → o ∉ E m2`.
  The Mathlib lemma `Set.disjoint_left` says `Disjoint A B ↔ ∀ a ∈ A, a ∉ B`;
  rewriting with it is the whole proof.
* `refutes_of_mem_of_disjoint`: if `o ∈ E m'` and `E m'` is disjoint from
  `E m` for every `m ∈ H`, then `o` refutes `H`. This is **the workhorse**: to
  show an observation refutes `H`, show it is an outcome of some rival model
  whose outcomes never overlap `H`'s.
* `discriminates_compl`: discriminating `H` is the same as discriminating its
  complement `Hᶜ`, because `Disjoint` is symmetric (`.symm`).
* `discriminates_implies_informative`:
  ```lean
  theorem discriminates_implies_informative (h : discriminates E H)
      (hne : ∃ m ∉ H, (E m).Nonempty) : informative E H
  ```
  **Choosing the right hypothesis.** A first guess might be "some `m ∈ H` has
  an outcome", but that is wrong: an outcome of a model *inside* `H` can never
  refute `H` (that model allows it!). What we need is a model **outside** `H`
  that can produce some outcome `o`. Discrimination then says no model in `H`
  allows `o`, so `o` refutes `H`. The mirror version
  `discriminates_implies_informative_compl` uses a model inside `H` to get
  `informative E Hᶜ`.
* `discriminates_of_pairwise_disjoint`: if different models always have
  disjoint outcome sets, the experiment discriminates *every* `H`. (If
  `m1 ∈ H` and `m2 ∉ H`, they can't be the same model.)

## 2. Basic.lean: from biology to definitions

### Models

```lean
inductive Model where
  | Conservative | Semiconservative | UniformDispersive
  deriving DecidableEq
```

An `inductive` type with three constructors is Lean's way of saying "a model
is exactly one of these three things". `deriving DecidableEq` lets Lean
compute whether two models are equal.

### Observations

`abbrev Obs : Type := Finset ℚ`: an observation is a finite set of band
positions, using rational numbers (`ℚ`) so `norm_num` can do exact arithmetic.
On this scale, light (¹⁴N/¹⁴N) DNA is at `0`, hybrid (¹⁵N/¹⁴N) at `1/2`,
heavy (¹⁵N/¹⁵N) at `1`. The setting is `abbrev MS : Setting := ⟨Model, Obs⟩`.

### Ideal bands

Work out what each model predicts if you start with all-heavy DNA and copy it
in light medium:

| | Generation 1 | Generation 2 |
|---|---|---|
| Conservative | heavy + light: `{0, 1}` | `{0, 1}` (light : heavy = 3 : 1) |
| Semiconservative | all hybrid: `{1/2}` | `{0, 1/2}` (1 : 1) |
| Uniform dispersive | all half-heavy: `{1/2}` | all quarter-heavy: `{1/4}` |

These are `ideal1` and `ideal2`, defined by pattern matching on the model.

### Measurement error

Real bands are never exactly at `1/2`. So an experiment allows an
observation if it matches the ideal bands *up to an error* `ε`:

```lean
def Matches (ε : ℚ) (I o : Finset ℚ) : Prop :=
  (∀ b ∈ o, ∃ c ∈ I, |b - c| ≤ ε) ∧ (∀ c ∈ I, ∃ b ∈ o, |b - c| ≤ ε)

def bandExperiment (ideal : Model → Finset ℚ) (ε : ℚ) : Experiment MS :=
  fun m => {o | Matches ε (ideal m) o}

def E1 (ε : ℚ) : Experiment MS := bandExperiment ideal1 ε
def E2 (ε : ℚ) : Experiment MS := bandExperiment ideal2 ε
```

In words: every band we see is near a predicted band, *and* every predicted
band shows up near something we see. Both halves matter. Without the second
half, seeing nothing at all would fit every model.

### The key lemma

```lean
theorem not_matches_both {ε : ℚ} {I J : Finset ℚ} (c : ℚ) (hc : c ∈ I)
    (hfar : ∀ d ∈ J, 2 * ε < |c - d|) (o : Finset ℚ) :
    Matches ε I o → ¬ Matches ε J o
```

If one ideal band `c` of `I` is more than `2ε` from every ideal band of `J`,
no observation matches both. Proof, step by step:

1. `rintro ⟨-, hcover⟩ ⟨hclose, -⟩`: assume `o` matches `I` (we keep only the
   "every ideal band is seen" half, `hcover`) and matches `J` (we keep only
   the "every seen band is near an ideal band" half, `hclose`).
2. `obtain ⟨b, hb, hbc⟩ := hcover c hc`: some seen band `b` is within `ε` of `c`.
3. `obtain ⟨d, hd, hbd⟩ := hclose b hb`: that `b` is within `ε` of some `d ∈ J`.
4. `rw [abs_le] at hbc hbd` turns `|b - c| ≤ ε` into `-ε ≤ b - c ∧ b - c ≤ ε`.
   `rw [lt_abs]` turns `2ε < |c - d|` into `2ε < c - d ∨ 2ε < -(c - d)`.
5. `rcases h with h | h <;> linarith`: in each case, adding up the
   inequalities gives a contradiction. `linarith` does that adding for us.

This is just the triangle inequality, done by hand so a beginner can see it.
`disjoint_of_far` repackages it as `Disjoint (E m1) (E m2)`.

## 3. Generation1.lean

`obs1 : Obs := {1/2}`, the single hybrid band.

* `obs1_mem_semi`, `obs1_mem_disp`: `{1/2}` is exactly the ideal for both, so
  `matches_self` (each band is `0 ≤ ε` from itself) proves it.
* `E1_disjoint_cons_semi (hε : ε < 1/4)`: use `disjoint_of_far 1`. The
  conservative band `1` is `1/2` from the only semiconservative band `1/2`,
  and `2ε < 1/2` because `ε < 1/4`. Tactics: `simp [ideal1] at hd` finds
  `d = 1/2`; `subst` plugs it in; `norm_num` computes `|1 - 1/2| = 1/2`;
  `linarith` finishes using `hε`.
* **Theorem 1**, `gen1_refutes_conservative`: `apply refutes_of_mem_of_disjoint (obs1_mem_semi h0)`.
  Then we only need: for `m ∈ {Conservative}`, `E1 ε m` is disjoint from
  `E1 ε Semiconservative`. `simp at hm` turns `m ∈ {Conservative}` into
  `m = Conservative`, and the disjointness lemma finishes it.
* `gen1_discriminates_conservative` and `gen1_informative_conservative`
  (bonus): generation 1 already separates conservative from the others.
  We go through the other two models with `cases m2`.
* **Theorem 2**, `gen1_not_discriminates_semi`: `rw [not_discriminates]`,
  then pick `m1 = Semiconservative`, `m2 = UniformDispersive`, and show their
  outcome sets aren't disjoint with `Set.not_disjoint_iff` and the common
  outcome `obs1`. (`gen1_semi_eq_disp` even shows the two sets are *equal*,
  by `rfl`, because the ideal bands are the same.)

## 4. Generation2.lean

* Three disjointness lemmas, each using `disjoint_of_far`:
  - conservative vs. semi: band `1` is `1` from `0` and `1/2` from `1/2`;
  - conservative vs. dispersive: band `1/4` is `1/4` from `0` and `3/4` from `1`;
  - semi vs. dispersive: band `1/4` is `1/4` from `0` and from `1/2`.
  The closest gap is `1/4`, so we need `2ε < 1/4`, i.e. **`ε < 1/8`**.
  Each proof: `simp only [ideal2, Finset.mem_insert, Finset.mem_singleton] at hd`
  turns `d ∈ {0, 1/2}` into `d = 0 ∨ d = 1/2`; `rcases hd with rfl | rfl` splits
  the cases and substitutes; `norm_num` computes the absolute value; `linarith`
  finishes. `Disjoint.symm` flips the order when the far band is on the right.
* **Theorem 3**, `E2_pairwise_disjoint`: `cases m1 <;> cases m2` gives all 9
  pairs. `all_goals first | ... | ...` tries each option on each goal: the 3
  "same model" pairs contradict `m1 ≠ m2`, and the other 6 are our three
  lemmas or their `.symm`. Then `gen2_discriminates` follows from
  `discriminates_of_pairwise_disjoint`, for *every* hypothesis `H`, including
  the three singletons.
* **Theorem 4**, `gen2_refutes_cons_disp` / `gen2_result`: `obs2 = {0, 1/2}` is
  a semiconservative outcome (`matches_self`), so `refutes_of_mem_of_disjoint`
  plus pairwise disjointness refutes `{Conservative, UniformDispersive}`.
  The side goal `m ≠ Semiconservative` comes from `rcases hm with rfl | rfl <;> simp`.
* `gen2_not_refutes_semi` (via `not_refutes`): the data are consistent with
  semiconservative replication.
* `gen2_semi_outcome_excludes_rivals` (via `discriminates_iff`): *any*
  semiconservative-looking generation-2 outcome, not just the exact `{0, 1/2}`,
  is impossible under both rivals. This matters because real measurements are
  never exactly `0` and `1/2`.
* `gen2_not_disjoint_at_eighth`: the bound is **sharp**. With `ε = 1/8`, the
  observation `{1/8, 3/8}` fits both semiconservative (`1/8` near `0`, `3/8`
  near `1/2`) and dispersive (both within `1/8` of `1/4`). Proved by unfolding
  everything with `simp only [...]` and letting `norm_num [abs_le]` check the
  arithmetic.

## 5. Modeling assumptions and caveats

1. **Bounded error is an assumption.** The paper's "50 ± 2%" is a statistical
   error (a typical spread), not a promise that no band is ever off by more.
   We model it as a hard bound `ε` and state in every theorem exactly what `ε`
   we need: `0 ≤ ε < 1/4` for generation 1, `0 ≤ ε < 1/8` for generation 2.
   The reported 2% (`ε = 1/50`) is comfortably inside both ranges.
2. **Idealized observations.** `obs1 = {1/2}` and `obs2 = {0, 1/2}` are the
   *ideal* readings. The disjointness theorems cover any reading within `ε`,
   so a real reading like `0.49` is also handled (see
   `gen2_semi_outcome_excludes_rivals`).
3. **Only band positions, not intensities.** We ignore how *much* DNA is in
   each band (1 : 1 vs 3 : 1). Positions alone are already enough for every
   theorem here. Adding intensities as a second observable would be a natural
   extension.
4. **Uniform dispersive only.** "Dispersive" here means old and new material
   is spread *evenly*, so every generation-2 molecule is exactly 1/4 heavy.
   Messier dispersive schemes could spread bands out; we don't model those.
   (Historically, ruling out dispersive replication fully took later work,
   such as heat-denaturation experiments.)
5. **"Every ideal band is seen."** We assume no predicted band is missed.
   A very faint band (for example the conservative model's heavy band in later
   generations) could in practice go unseen.
6. **Positions are on an idealized linear scale** from light to heavy. The
   paper measures positions in a density gradient, which is close to linear
   over this small range.

## 6. What was hard, and what didn't work at first

* **`def` vs `abbrev`.** Defining `Hypothesis` with `def` broke `m ∈ H` and
  `Hᶜ` ("failed to synthesize Membership"). Switching to `abbrev` fixed it.
  The same thing happened with `def MS : Setting`: `simp` failed on
  `m ∈ {Conservative}` with a confusing "application type mismatch" between
  `MS.Model` and `Model`. Making `MS` an `abbrev` fixed that too.
* **Argument order in `discriminates_iff`.** The statement is
  `∀ m1 ∈ H, ∀ m2 ∉ H, ∀ o, ...`, so `o` comes *after* `m2`. Our first
  attempt passed `o` too early and got a type error.
* **Linter noise.** Mathlib's style linters (spacing around `/`, "flexible
  `simp`") produced lots of warnings that are about Mathlib's house style,
  not correctness. We turned them off in `lakefile.toml` so the build output
  stays readable for a teaching project.
* **Proving disjointness directly** by unfolding `Matches` for each pair of
  models would have meant six messy case analyses. Proving one general
  separation lemma (`not_matches_both`) first made every pair a three-line
  proof. That was the main design win.
* **Choosing the hypothesis of `discriminates_implies_informative`.** The
  natural first guess (a model inside `H` has an outcome) is false. You
  need a model *outside* `H` with an outcome.
