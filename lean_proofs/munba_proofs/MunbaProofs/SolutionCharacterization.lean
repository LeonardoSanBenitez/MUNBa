import MunbaProofs.Optimality

/-!
# Theorem 2.5 (Solution characterization)

`catalog.json`'s `theorem_2_5_solution_characterization`. Paper statement: the coefficient vector
`α = (α_r, α_f)` from Theorem 2.3 is exactly the (elementwise-reciprocal) fixed point of the 2x2
Gram-matrix equation `G^T G α = 1/α` (Eq. 6), i.e. writing it out (Eq. 7):

  `α_r ‖g_r‖² + α_f ⟪g_f,g_r⟫ = 1/α_r`,
  `α_f ‖g_f‖² + α_r ⟪g_f,g_r⟫ = 1/α_f`.

## Direct corollary of Theorem 2.3, no new machinery needed

The paper's own proof is pure substitution: dot Theorem 2.3's characterization
`g̃* = α_r g_r + α_f g_f` with `g_r` and with `g_f`, using bilinearity of the inner product. That
is exactly what this file does — a bilinearity computation, no calculus. `catalog.json`'s
`known_issues_in_paper` flags the paper's own "up to scaling" qualifier on this theorem as sitting
oddly against Theorem 2.3's proof, which pins `α_r, α_f` down EXACTLY (not up to a common
scalar) — this file inherits `Optimality.lean`'s resolution of that (the `ε=√2` normalization) and
states Theorem 2.5 as an EXACT equality throughout, consistent with `theorem_2_3_optimality_
condition`'s own conclusion.

The `1/α_r`, `1/α_f` on the right-hand side are literally `utility g_r gt`, `utility g_f gt`
themselves — this is immediate from how `α_r, α_f` were DEFINED in `Optimality.lean`
(`α_r := (utility g_r gt)⁻¹`), not a separate fact to prove; the real content of this theorem is
the LEFT-hand side (the Gram-matrix expression) matching them.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 2.5 (Solution characterization), `catalog.json`'s
`theorem_2_5_solution_characterization`. Given Theorem 2.3's characterization
`gt = α_r • g_r + α_f • g_f` (with `α_r := (u_r gt)⁻¹`, `α_f := (u_f gt)⁻¹`), the coefficients
satisfy the paper's 2x2 Gram-matrix system (Eq. 7). -/
theorem theorem_2_5_solution_characterization (g_r g_f gt : V)
    (hchar : gt = (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f) :
    (utility g_r gt)⁻¹ * ‖g_r‖ ^ 2 + (utility g_f gt)⁻¹ * ⟪g_f, g_r⟫ = utility g_r gt ∧
      (utility g_f gt)⁻¹ * ‖g_f‖ ^ 2 + (utility g_r gt)⁻¹ * ⟪g_f, g_r⟫ = utility g_f gt := by
  have key1 : (utility g_r gt : ℝ) =
      (utility g_r gt)⁻¹ * ‖g_r‖ ^ 2 + (utility g_f gt)⁻¹ * ⟪g_f, g_r⟫ := by
    change (⟪g_r, gt⟫ : ℝ) = _
    conv_lhs => rw [hchar]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm g_f g_r]
  have key2 : (utility g_f gt : ℝ) =
      (utility g_f gt)⁻¹ * ‖g_f‖ ^ 2 + (utility g_r gt)⁻¹ * ⟪g_f, g_r⟫ := by
    change (⟪g_f, gt⟫ : ℝ) = _
    conv_lhs => rw [hchar]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  exact ⟨key1.symm, key2.symm⟩

end Munba
