# Yquilibrium: Lean 4 formalization

![Lean build](https://github.com/jkg7866/Yquilibrium-lean/actions/workflows/lean_action_ci.yml/badge.svg)

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4), of the results in

> Jacob K. Goeree, *Yquilibrium*, version of 23 November 2026.

Each result in the paper is stated as a Lean theorem and proved from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry`, and no axiom has been added. The one exception is Kakutani's fixed-point theorem, which is not in Mathlib: Theorem 2(c) and Walrasian existence take it as an explicit hypothesis (see below).

## Checking the proofs

Install Lean through [elan](https://github.com/leanprover/elan) and git, then run:

```
lake exe cache get      # download precompiled Mathlib
lake build              # check every proof; ends with "Build completed successfully"
lake env lean Check.lean
```

The last command prints the axioms each result depends on. Every line should read `[propext, Classical.choice, Quot.sound]`.

Toolchain: `leanprover/lean4:v4.37.0-rc1`. Mathlib is pinned to commit `6ebcce37335bcb6bca64596e5d57bb3035648030`.

## Results

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (minimum income μ) | `mu_nonneg`, `mu_le_dot`, `mu_concave`, `mu_smul`, `mu_mono_pref`, `mu_strict`, `mu_usc` | `Basic.lean` |
| Lemma 2(i)–(ii) | `mu_perturb`, `free_large` | `Theorem1.lean` |
| Theorem 1 | `theorem1` | `Theorem1.lean` |
| Lemma 3 | `Y_nonneg`, `root_pos_pareto`, `optimal_mu`, `optimal_of_mu`, `root_iff` | `Roots.lean` |
| Theorem 2, existence; (a); (b) | `theorem2_exists`, `theorem2_a`, `theorem2_b` | `Roots.lean` |
| Theorem 2(c) | `theorem2_c`, `walrasianFor_exists` | `Existence.lean` |
| Walrasian equilibrium exists for the endowments ω | `walrasian_exists` | `Existence.lean` |
| Corollary 1(a) | `corollary1_a` | `Roots.lean` |
| Corollary 1(b) | `corollary1_b_weak` (and `corollary1_b`) | `Welfare2.lean` |
| Theorem 3 | `theorem3`, `theorem3_attain` | `Duality.lean` |
| Remark 1 | `remark1_lower`, `remark1_min_exists`, `remark1_eq`, `remark1_pareto` | `DeadLoss.lean` |
| Lemma 4 | `lemma4_nonneg`, `lemma4_roots`, `lemma4_convex` | `EisenbergGale.lean` |
| Proposition 1(a)–(c) | `prop1_a`, `prop1_b`, `prop1_c` | `Replica.lean` |
| Theorem 4: invariance, individual rationality, feasibility, barter | `invariance`, `path_IR`, `path_exact`, `barter` | `Dynamic.lean` |
| Theorem 4: almost-sure convergence | `theorem4` | `Theorem4.lean` |

Supporting files:
- `Convergence.lean`, `Berge.lean`, `Calculus.lean`, `Step1.lean`: the deterministic steps of Theorem 4.
- `ProbLemma.lean`: Lévy's extension of the Borel–Cantelli lemma, in the form the proof uses.
- `Measurable.lean`: measurability of the dynamic.
- `CES2.lean`: the numerical bounds for Proposition 1.

## Modelling choices a reader should know

- **Preferences** (`Pref`, `Basic.lean`) are complete, transitive and continuous on ℝ^K₊, and monotone in the two senses of Section 2: y ≫ x implies y ≻ x; and if x ≻ 0, y ≥ x and y ≠ x, then y ≻ x.
- **Kakutani's fixed-point theorem** is the hypothesis `Kakutani V` in `Existence.lean`, used in `theorem2_c`, `walrasianFor_exists` and `walrasian_exists`. It is a theorem for every finite-dimensional real vector space; it is assumed here only because Mathlib does not yet contain it (nor Brouwer's theorem).
- **Theorem 2(c)** is proved directly for fixed incomes m (a Fisher market), not by reduction to an Arrow–Debreu economy with endowments mᵢW. The same argument, with incomes ⟨p|ωᵢ⟩, gives `walrasian_exists`.
- **Theorem 4** takes the draws (proposer, price, trade size, order) to be i.i.d. with law ν. The proof uses one condition on ν (`FullSupport`): for every pair i ≠ j, every open set of prices meeting the interior of Σ_K(W) and every interval of trade sizes in (0,1], the event "i proposes at such a price and size, and j is asked first" has positive probability. `fullSupport_of_indep` shows that this follows from the paper's assumptions when (proposer, order), price and trade size are independent.
- **Theorem 3** takes the VPS over all prices in Σ_K(W). Where a price is zero, indirect utility can be +∞; such vectors are never minimal, and the Lean VPS keeps only the finite ones (utility bounded on each budget set). This is needed because Mathlib assigns a junk value, not +∞, to the supremum of an unbounded set.
- **Corollary 1(b)** concerns weakly Pareto-optimal allocations. `corollary1_b`, for Pareto-optimal allocations, is derived from it.
