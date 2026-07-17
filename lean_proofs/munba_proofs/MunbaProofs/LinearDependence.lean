import MunbaProofs.Basic

/-!
# Lemma 2.4 (Linear dependence) — the elementary fact actually load-bearing in MUNBa

`catalog.json`'s `lemma_2_4_linear_dependence`. Paper statement: at a Pareto stationary point,
`g_r` and `g_f` are linearly dependent. The paper's own proof imports an external "first-order
optimality condition for Pareto optimality" (citing Ye & Liu, UAI 2022, and Roy–So–Ma,
arXiv:2308.02145) and never itself defines "Pareto stationary point."

## Why this file does NOT formalize Lemma 2.4 as literally stated

Prior research (2026-07-15, see `munba/README.md` and this project's own `PLAN-LEAN-PROOFS.md`)
found: (1) no existing Lean/Isabelle/Coq formalization of Pareto-stationarity exists anywhere —
genuinely open territory, not attempted here; (2) MORE IMPORTANTLY, grepping the paper's own
LaTeX source confirmed Lemma 2.4 has no `\label` and is never cross-referenced anywhere else in
the paper — its own proof, and Theorem 2.10's closing argument (the only other place this content
is used), both derive "`g_r, g_f` linearly dependent" directly from the vanishing of a specific
POSITIVE combination `α_r g_r + α_f g_f = 0`, NEVER actually invoking the cited external Pareto
condition's full generality. The external citation is decorative in this paper, not load-bearing.

This file formalizes the elementary linear-algebra fact both Lemma 2.4's own proof and Theorem
2.10's closing argument actually reduce to, once the external condition is instantiated: a
positive combination of two vectors vanishing forces linear dependence. Formalizing "Pareto
stationarity" as a general notion (which would need inventing a definition the paper itself never
gives, then proving or importing Ye–Liu/Roy–So–Ma's theorem) remains explicitly NOT done, and NOT
needed for anything MUNBa itself actually uses.
-/

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The elementary fact behind Lemma 2.4 and Theorem 2.10's closing step: if a combination
`α_r • g_r + α_f • g_f` with `α_r ≠ 0` vanishes, `g_r` is a scalar multiple of `g_f` — i.e.
`g_r, g_f` are linearly dependent. -/
theorem gr_linearlyDependent_of_combination_eq_zero {g_r g_f : V} {α_r α_f : ℝ}
    (hα_r : α_r ≠ 0) (heq : α_r • g_r + α_f • g_f = 0) :
    g_r = (-α_f / α_r) • g_f := by
  have h1 : α_r • g_r = -(α_f • g_f) := by
    have h0 : α_r • g_r = α_r • g_r + α_f • g_f - α_f • g_f := by abel
    rw [h0, heq, zero_sub]
  have h2 : g_r = α_r⁻¹ • (α_r • g_r) := by rw [smul_smul, inv_mul_cancel₀ hα_r, one_smul]
  rw [h2, h1, smul_neg, smul_smul, neg_div, neg_smul]
  congr 2
  ring

/-- Lemma 2.4 (Linear dependence), `catalog.json`'s `lemma_2_4_linear_dependence`, formalized via
the route above: at a point where the bargained combination `α_r g_r + α_f g_f` vanishes (the
content Ye–Liu/Roy–So–Ma's imported condition actually supplies here, instantiated directly
rather than through the general external theorem), `g_r` and `g_f` are linearly dependent. -/
theorem lemma_2_4_linear_dependence {g_r g_f : V} {α_r α_f : ℝ}
    (hα_r_pos : 0 < α_r) (heq : α_r • g_r + α_f • g_f = 0) :
    ∃ ζ : ℝ, g_r = ζ • g_f :=
  ⟨-α_f / α_r, gr_linearlyDependent_of_combination_eq_zero (ne_of_gt hα_r_pos) heq⟩

end Munba
