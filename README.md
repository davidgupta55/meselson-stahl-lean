# Meselson–Stahl (1958) in Lean 4

A Lean 4 + Mathlib formalization of the logic of the **Meselson–Stahl
experiment**, written in (a re-creation of) Prof. Eric Klavins's
scientific-method framework.

> M. Meselson and F. W. Stahl, "The Replication of DNA in *Escherichia coli*",
> *PNAS* 44(7):671–682, 1958.
> <https://www.pnas.org/doi/10.1073/pnas.44.7.671> ·
> [open PDF](https://www.mun.ca/biology/scarr/Meselson_&_Stahl_1958_PNAS_44-671.pdf)

By David Gupta (Nico), written with AI assistance as a UW Math AI Lab project.
MIT licensed.

## The experiment in one paragraph

E. coli were grown on heavy nitrogen (¹⁵N), then moved to light nitrogen
(¹⁴N). After each generation the DNA was spun in a cesium chloride density
gradient. Band positions are read on a scale from `0` (light) to `1` (heavy).
Generation 1 showed one hybrid band at 50 ± 2%. Generation 2 showed hybrid and
light bands in equal amounts. Three models compete: **conservative**,
**semiconservative**, and **(uniform) dispersive** replication.

## What is proved

Files:

| File | Contents |
|---|---|
| [`MeselsonStahl/Framework.lean`](MeselsonStahl/Framework.lean) | `Setting`, `Experiment`, `Hypothesis`, `refutes`, `informative`, `discriminates`, and general lemmas (`not_refutes`, `not_discriminates`, `discriminates_iff`, `discriminates_implies_informative`, …) |
| [`MeselsonStahl/Basic.lean`](MeselsonStahl/Basic.lean) | the three models, ideal bands for generations 1 and 2, the bounded-error experiments `E1 ε`, `E2 ε`, and the key separation lemma |
| [`MeselsonStahl/Generation1.lean`](MeselsonStahl/Generation1.lean) | Theorems 1 and 2 |
| [`MeselsonStahl/Generation2.lean`](MeselsonStahl/Generation2.lean) | Theorems 3 and 4, plus sharpness of `ε < 1/8` |

Main theorems (`ε` is the assumed maximum measurement error):

```lean
-- 1. Generation 1's single band at 1/2 refutes conservative replication.
theorem gen1_refutes_conservative {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/4) :
    refutes (E1 ε) {Conservative} obs1

-- 2. Generation 1 cannot tell semiconservative from dispersive.
theorem gen1_not_discriminates_semi {ε : ℚ} (h0 : 0 ≤ ε) :
    ¬ discriminates (E1 ε) {Semiconservative}

-- 3. In generation 2 the three models' outcome sets are pairwise disjoint,
--    so generation 2 discriminates every hypothesis.
theorem E2_pairwise_disjoint {ε : ℚ} (hε : ε < 1/8) :
    ∀ m1 m2 : Model, m1 ≠ m2 → Disjoint (E2 ε m1) (E2 ε m2)
theorem gen2_discriminates {ε : ℚ} (hε : ε < 1/8) (H : Hypothesis MS) :
    discriminates (E2 ε) H

-- 4. Generation 2's bands {0, 1/2} refute "conservative or dispersive"
--    and are a semiconservative outcome.
theorem gen2_result {ε : ℚ} (h0 : 0 ≤ ε) (hε : ε < 1/8) :
    refutes (E2 ε) {Conservative, UniformDispersive} obs2 ∧
      obs2 ∈ E2 ε Semiconservative
```

Each comes with a concrete `ε = 1/50` (the reported ±2%) instance, e.g.
`gen1_refutes_conservative_2pct` and `gen2_result_2pct`. The bound `1/8` is
sharp: `gen2_not_disjoint_at_eighth` shows that with `ε = 1/8` the
semiconservative and dispersive outcome sets overlap.

**Modeling assumption:** the ±2% in the paper is a statistical error, not a
hard bound. Treating it as a hard bound `ε` is an explicit assumption; see
[`NOTES.md`](NOTES.md).

No `sorry`. The main theorems depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Building

```
lake exe cache get && lake build
```

(`lake exe cache get` downloads Mathlib's prebuilt files so you don't have to
compile Mathlib yourself.)

See [`NOTES.md`](NOTES.md) for a beginner-level walk-through of every
definition and proof.
