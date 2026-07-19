# Lean 4 / Mathlib formalization of MUNBa's theoretical results

Machine-checked (Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)) proofs of MUNBa's mathematical results: Lemmas 2.1, 2.2, 2.4, 2.8, 6.1, Theorems 2.3, 2.5, 2.6, 2.9, 2.10, and Remark 2.7.

## Status

All 11 results are formalized, with zero `sorry` and `#print axioms` reporting only the standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`):

- **Lemma 2.1** (Feasibility) — `Feasibility.lean`
- **Lemma 2.2** (Cone property) — `ConeProperty.lean`
- **Lemma 6.1** (Lipschitz-smoothness descent lemma) — `DescentLemma.lean`
- **Theorem 2.3** (Optimality condition, the KKT-style stationarity result) — `NashObjective.lean` + `SphereExtremum.lean` + `Optimality.lean`
- **Theorem 2.5** (Solution characterization) — `SolutionCharacterization.lean`
- **Lemma 2.8** (Lower bound) — `LowerBound.lean`
- **Theorem 2.9** (Pareto improvement) — `ParetoImprovement.lean`
- **Theorem 2.6** (Closed-form solution) — `ClosedFormSolution.lean`
- **Remark 2.7** (degenerate Gram matrix) — `DegenerateGram.lean`
- **Lemma 2.4** (Linear dependence) — `LinearDependence.lean`. Proved from a Pareto-stationarity hypothesis (no common strict descent direction for $g_r, g_f$) via a two-vector instance of Gordan's theorem of the alternative, with a short constructive proof (solve the $2 \times 2$ Gram system via Cramer's rule for an explicit witness direction) rather than general convex-cone machinery.
- **Theorem 2.10** (Convergence) — `Convergence.lean`. Both halves proved; see the dedicated section below for the hypotheses used.

(Lemma 2.8 and Theorem 2.9 were proved before Theorem 2.6, out of the paper's own numbering order — neither depends on it, so both were tractable earlier.)

## How to build

Requires a Lean 4 toolchain (`elan`/`lake`). Run `lake build` in this folder.

## What is proved

- `Basic.lean` — shared setup. Works in an arbitrary real inner product space $V$ rather than committing to a specific $\mathbb{R}^n$/$\mathbb{R}^d$ (the paper uses both). Models the utility functions $u_r$, $u_f$ (Eqs. 2-3) as unary in the candidate joint direction, with each player's gradient as fixed data.

- `Feasibility.lean` — Lemma 2.1. Proves the feasible set is non-empty under the paper's hypothesis (gradients conflict but aren't diametrically opposed). Uses a simpler witness than the paper's segment-parametrization argument (documented in the file); the resulting proof only needs the weaker one-sided form of the hypothesis.

- `ConeProperty.lean` — Lemma 2.2. States and proves the general fact underlying it (the positivity region of any pair of degree-1-positively-homogeneous functions is a cone), then derives the paper's specific statement as a corollary.

- `DescentLemma.lean` — Lemma 6.1 (the Lipschitz-smoothness descent lemma). This result is a special case of general facts already in Mathlib, so rather than reproving it from scratch, this file states Lemma 6.1 in the paper's own notation and shows how it follows by specializing two existing Mathlib theorems (`HasGradientAt` and a general derivative-comparison "fencing" theorem); the docstring names both and explains the correspondence.

- **Theorem 2.3** (Optimality condition) — the paper's KKT-style stationarity result, built as three files: `NashObjective.lean` (the objective's scale-shift identity, plus a proof that the ball constraint is active at the optimum); `SphereExtremum.lean` (the two positivity constraints are dropped, since the feasible set is open and they are never binding at a feasible point); `Optimality.lean` (the Lagrange-multiplier assembly, specializing Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d` together with `hasStrictFDerivAt_norm_sq` and `HasStrictFDerivAt.log`, all named and explained in the file's docstring). One clarification made explicit in the file: the paper's boxed conclusion ($\tilde{g}^* = \alpha_r g_r + \alpha_f g_f$) is reached via a "set $\lambda = 1$ as a normalization step"; working through the argument shows this holds as an exact equality at the ball radius $\varepsilon = \sqrt{2}$ (consistent with $\lVert \tilde{g}^* \rVert^2 = 2$ appearing in two of the paper's later proofs), which the file takes as an explicit hypothesis.

- `SolutionCharacterization.lean` — Theorem 2.5. A direct algebraic corollary of Theorem 2.3's conclusion: dotting $\tilde{g}^* = \alpha_r g_r + \alpha_f g_f$ with $g_r$ and $g_f$ gives the paper's $2 \times 2$ Gram-matrix system (Eq. 7) via bilinearity, no new machinery needed.

- `LowerBound.lean` — Lemma 2.8. Proves $\lVert \tilde{g}^* \rVert^2 = 2$ as its own reusable lemma, then Cauchy-Schwarz plus the gradient-norm bound gives the paper's $\alpha_i \ge 1/(\sqrt{2}\, M)$ bound directly.

- `ParetoImprovement.lean` — Theorem 2.9. Factors the paper's symmetric-in-$r,f$ argument into a single-player descent step (proved once, reusing Lemma 6.1's descent inequality and Lemma 2.8's $\lVert \tilde{g}^* \rVert^2 = 2$), applied twice to get the two-player theorem.

- `ClosedFormSolution.lean` — Theorem 2.6. This file proves the paper's stated closed form via a route found while planning: multiplying Theorem 2.5's two equations through by $\alpha_r$, $\alpha_f$ (no division) gives two expressions both equal to $1$, so $\alpha_r^2 \lVert g_r \rVert^2 = \alpha_f^2 \lVert g_f \rVert^2$ directly — no quartic elimination and no sign case-split (since $\alpha_r, \alpha_f > 0$ is already known from Theorem 2.3). Checked symbolically and numerically that this reproduces the paper's formula exactly before writing any Lean.

- `DegenerateGram.lean` — Remark 2.7. Only the remark's mathematical claim (linearly dependent gradients make the Gram matrix singular) is proved; the noise-injection and $\alpha = [0.5, 0.5]$ heuristics the remark also mentions are engineering choices, not formalized.

- `LinearDependence.lean` — Lemma 2.4, proved from a "no common strict descent direction" Pareto-stationarity hypothesis. This file proves the needed two-vector case directly and constructively (Gordan's theorem of the alternative, solved via the same $2 \times 2$ Gram-system technique as Theorem 2.6), which is short and self-contained.

## Theorem 2.10 (Convergence)

`Convergence.lean` proves the full theorem, in two parts:

1. `theorem_2_10_combined_loss_converges` — unconditional: given each player's loss along the MUNBa iteration is non-increasing (Theorem 2.9) and bounded below, the combined loss converges. Standard real-analysis.
2. `theorem_2_10_stationarity` / `theorem_2_10_convergence` — the paper's other half, that the trajectory's limit point is a Pareto stationary point. We formalize the paper's claim exactly as published, with two steps taken as explicit Lean hypotheses (the same way `Optimality.lean` takes existence of the constrained maximizer as a hypothesis): that the trajectory itself converges to $\theta^*$, and that some positive combination of the two gradients vanishes at $\theta^*$. Given those, Pareto stationarity follows by reusing `LinearDependence.lean`'s `gr_linearlyDependent_of_combination_eq_zero`, matching the paper's closing sentence. Both hypotheses are documented in-file.

Full mathematical detail — formal statements, hypotheses, complete proof transcriptions, and notes on the published proofs — is in `catalog.json` in this folder.
