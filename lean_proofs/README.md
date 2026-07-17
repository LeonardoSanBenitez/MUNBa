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
- **Lemma 2.8** (Lower bound) — `MunbaProofs/LowerBound.lean`
- **Theorem 2.9** (Pareto improvement) — `MunbaProofs/ParetoImprovement.lean`
- **Theorem 2.6** (Closed-form solution) — `MunbaProofs/ClosedFormSolution.lean`
- **Remark 2.7** (degenerate Gram matrix) — `MunbaProofs/DegenerateGram.lean`
- **Lemma 2.4** (Linear dependence) — `MunbaProofs/LinearDependence.lean`. Proved from an actual
  Pareto-stationarity hypothesis (no common strict descent direction for `g_r, g_f`) via a
  two-vector instance of Gordan's theorem of the alternative, with a short constructive proof
  (solve the 2×2 Gram system via Cramer's rule for an explicit witness direction) rather than
  general convex-cone machinery. An earlier pass at this file proved only a weaker special case;
  see the file's own docstring for what changed and why.

**Theorem 2.10** (Convergence) is HALF done — see `MunbaProofs/Convergence.lean` and "Not yet
formalized" below. (Lemma 2.8 and Theorem 2.9 were proved before Theorem 2.6, out of the paper's
own numbering order — neither depends on it, so both were tractable earlier; see the working
plan for the reasoning.)

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

- `MunbaProofs/LowerBound.lean` — Lemma 2.8. Proves `‖g̃*‖²=2` as its own reusable lemma (via the
  "corrected chain" `catalog.json` recommends, since the paper's own Eq. 37 is confirmed mistyped
  in the authors' own LaTeX source), then Cauchy-Schwarz plus the gradient-norm bound gives the
  paper's `α_i ≥ 1/(√2 M)` bound directly.

- `MunbaProofs/ParetoImprovement.lean` — Theorem 2.9. Factors the paper's symmetric-in-`r,f`
  argument into a single-player descent step (proved once, reusing Lemma 6.1's descent inequality
  and Lemma 2.8's `‖g̃*‖²=2`), applied twice to get the two-player theorem.

- `MunbaProofs/ClosedFormSolution.lean` — Theorem 2.6, the hardest item in the catalog (the
  paper's own route is quartic elimination → quadratic formula → an informally-justified sign
  choice, with two flagged gaps: an unaddressed `⟪g_r,g_f⟫=0` case, and the sign choice itself
  asserted rather than proved). This file proves the paper's own stated closed form via a
  genuinely simpler route found while planning: multiplying Theorem 2.5's two equations through
  by `α_r`, `α_f` (no division) gives two expressions both equal to `1`, so `α_r²‖g_r‖² =
  α_f²‖g_f‖²` directly — no quartic, no case split, and no sign ambiguity (since `α_r, α_f > 0`
  is already known from Theorem 2.3, not something being solved for). Independently checked
  (symbolically and numerically) that this reproduces the paper's own formula exactly before
  writing any Lean.

- `MunbaProofs/DegenerateGram.lean` — Remark 2.7. Only the remark's actual mathematical claim
  (linearly dependent gradients make the Gram matrix singular) is proved; the noise-injection and
  `α=[0.5,0.5]` heuristics the remark also mentions are engineering choices, not formalized.

- `MunbaProofs/LinearDependence.lean` — Lemma 2.4, proved from an actual "no common strict
  descent direction" Pareto-stationarity hypothesis. The paper's own proof imports an external
  first-order Pareto-optimality condition (Ye–Liu 2022 / Roy–So–Ma 2023); this file instead
  proves the needed two-vector case directly and constructively (Gordan's theorem of the
  alternative, solved via the same 2×2-Gram-system technique as Theorem 2.6), which turned out to
  be short and self-contained rather than requiring either the external citation or Mathlib's
  general convex-cone duality machinery (`Analysis/Convex/Cone/InnerDual`, which does have
  Farkas'-lemma-equivalent tools, just more than needed for exactly two vectors).

## Theorem 2.10 (Convergence) — read before citing as done or not done

`MunbaProofs/Convergence.lean` proves HALF of Theorem 2.10: given each player's loss along the
MUNBa iteration is non-increasing (Theorem 2.9) and bounded below, the COMBINED loss converges —
standard real-analysis, no real difficulty. The paper's OTHER half — that the limit point is a
(Pareto) stationary point, via `η^(t)g̃^(t)→0` — is explicitly NOT formalized here.
`catalog.json`'s own reading of the paper flags this second half as "the least rigorous step in
the paper's entire proof section": asserted by the paper, not derived. Attempted the natural
telescoping argument directly (not just asserted the gap) and confirmed it does NOT close without
an extra hypothesis: the guaranteed per-step decrease is proportional to `1/α_i`, and `α_i` has no
proven upper bound (Lemma 2.8 only gives a lower one) — so the argument needs an explicit bound on
`α_r, α_f` along the trajectory (equivalently, the angle between the two gradients staying bounded
away from degenerate), which the paper never states. This is a genuine open design question (what
assumption to add, and whether that changes the theorem being proved), not a routine remaining
task.

Full mathematical detail — formal statements, hypotheses, complete proof transcriptions from the
paper, and known issues/typos found in the published proofs on close reading — lives in this
project's own working catalog, not duplicated here.
