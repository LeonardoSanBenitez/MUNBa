# Lean 4 / Mathlib formalization of MUNBa's theoretical results

Machine-checked (Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)) proofs of
the mathematical results in Wu & Harandi, *"MUNBa: Machine Unlearning via Nash Bargaining"*
(ICCV 2025, [arXiv:2411.15537](https://arxiv.org/abs/2411.15537)) — Lemmas 2.1, 2.2, 2.4, 2.8,
6.1, Theorems 2.3, 2.5, 2.6, 2.9, 2.10, and Remark 2.7 from the paper.

## Status

Work in progress. Proved so far, with zero `sorry` and `#print axioms` reporting only the
standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`):

- **Lemma 2.1** (Feasibility) — `MunbaProofs/Feasibility.lean`
- **Lemma 2.2** (Cone property) — `MunbaProofs/ConeProperty.lean`
- **Lemma 6.1** (Lipschitz-smoothness descent lemma) — `MunbaProofs/DescentLemma.lean`
- **Theorem 2.3** (Optimality condition, the KKT-style stationarity result) —
  `MunbaProofs/NashObjective.lean` + `MunbaProofs/SphereExtremum.lean` +
  `MunbaProofs/Optimality.lean`
- **Theorem 2.5** (Solution characterization) — `MunbaProofs/SolutionCharacterization.lean`

Theorems 2.6/2.9/2.10, Lemma 2.4, and Remark 2.7 are not yet formalized.

## How to build

Requires a Lean 4 toolchain (`elan`/`lake`). `cd` into `munba_proofs/` and run `lake build`. On
Windows, build from a short path — Mathlib's own file paths combined with a deeply nested
checkout can exceed `MAX_PATH`.

## What's proved so far, and how

- `MunbaProofs/Basic.lean` — shared setup. Works in an arbitrary real inner product space `V`
  rather than committing to a specific `ℝ^n`/`ℝ^d` (the paper itself is inconsistent about which
  it means where). Models the paper's utility functions `u_r`, `u_f` (Eqs. 2-3) as genuinely
  unary in the candidate joint direction, with each player's gradient as fixed data — the paper's
  own stated type signature for `u_r`/`u_f` doesn't match how they're actually used.

- `MunbaProofs/Feasibility.lean` — Lemma 2.1. Proves the feasible set is non-empty under the
  paper's hypothesis (gradients conflict but aren't diametrically opposed). Uses a different,
  simpler witness than the paper's own segment-parametrization argument (documented in the file);
  the resulting proof only needs the weaker one-sided form of the paper's hypothesis.

- `MunbaProofs/ConeProperty.lean` — Lemma 2.2. States and proves the general fact underlying it
  (the positivity region of any pair of degree-1-positively-homogeneous functions is a cone), then
  derives the paper's specific statement as a corollary.

- `MunbaProofs/DescentLemma.lean` — Lemma 6.1 (the Lipschitz-smoothness descent lemma). This
  result is a special case of general facts already in Mathlib, so rather than reproving it from
  scratch, this file states MUNBa's own Lemma 6.1 in the paper's own notation and shows explicitly
  how it follows by specializing two existing Mathlib theorems (`HasGradientAt` and a general
  derivative-comparison "fencing" theorem) — the file's docstring names both and explains the
  correspondence, so the mapping between the paper's claim and the library facts is legible on its
  own, not just "code that happens to compile."

- **Theorem 2.3** (Optimality condition) — the paper's KKT-style stationarity result, built as
  three files: `NashObjective.lean` (the objective's scale-shift identity, and a genuinely useful
  finding — a proof that the paper's own ball constraint must be active at the optimum, a gap in
  the PAPER's own proof, not just ours); `SphereExtremum.lean` (the paper's two positivity
  constraints can be dropped entirely, since they are never binding at any feasible point — a more
  fundamental reason than the paper's own complementary-slackness argument); `Optimality.lean`
  (the actual Lagrange-multiplier assembly, specializing Mathlib's
  `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d` together with `hasStrictFDerivAt_
  norm_sq` and `HasStrictFDerivAt.log`, all named and explained in the file's own docstring).
  One clarification worth being explicit about: the paper's proof reaches its boxed conclusion
  (`g̃* = α_r g_r + α_f g_f`) via a "set λ=1 as a normalization step" move that reads as a free
  choice but is not — working through the argument in full shows this holds as an exact equality
  only at a specific ball radius, `ε = √2`, never stated explicitly in the paper (though consistent
  with, and the real reason behind, `‖g̃*‖²=2` reappearing in two of the paper's own later proofs).
  This file takes `ε=√2` as an explicit hypothesis rather than leaving it an unexplained given.

- `MunbaProofs/SolutionCharacterization.lean` — Theorem 2.5. A direct algebraic corollary of
  Theorem 2.3's own conclusion: dotting `g̃* = α_r g_r + α_f g_f` with `g_r` and `g_f` gives the
  paper's 2x2 Gram-matrix system (Eq. 7) via bilinearity, no new machinery needed.

Full mathematical detail — formal statements, hypotheses, complete proof transcriptions from the
paper, and known issues/typos found in the published proofs on close reading — lives in this
project's own working catalog, not duplicated here.
