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

Everything else in the paper's theoretical results (Theorem 2.3's KKT optimality condition,
Theorems 2.5/2.6/2.9/2.10, Lemma 2.4, Lemma 6.1's descent lemma, Remark 2.7) is not yet
formalized.

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

Full mathematical detail — formal statements, hypotheses, complete proof transcriptions from the
paper, and known issues/typos found in the published proofs on close reading — lives in this
project's own working catalog, not duplicated here.
