import SolutionCharacterization

/-!
# Lemma 2.8 (Lower bound)

`catalog.json`'s `lemma_2_8_lower_bound`. Paper statement: if `‖g_i‖ ≤ M` for both players
`i ∈ {r,f}`, the bargaining coefficients cannot collapse to zero: `α_i ≥ 1/(√2 M)`.

## The corrected chain

`catalog.json`'s `known_issues_in_paper` notes that Eq. (37)'s middle lines wrap a squared norm
`‖·‖²` around a scalar (the dot product `(α_i g_i + α_j g_j)ᵀ g̃`). This file formalizes the
corrected reading: `‖g̃*‖² = 2` by direct bilinear expansion (the same computation Theorem 2.9's
proof uses in Eq. 41), then Cauchy-Schwarz and a one-line inversion give the bound.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The identity `‖g̃*‖² = 2`, reused by both this lemma and Theorem 2.9 (per `catalog.json`'s
recommendation not to duplicate it) — an immediate consequence of Theorem 2.3's characterization
`g̃* = α_r g_r + α_f g_f` together with `α_r = 1/u_r(g̃*)`, `α_f = 1/u_f(g̃*)`. -/
theorem norm_sq_eq_two (g_r g_f gt : V) (hr : 0 < utility g_r gt) (hf : 0 < utility g_f gt)
    (hchar : gt = (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f) :
    ‖gt‖ ^ 2 = 2 := by
  have h1 : (⟪gt, gt⟫ : ℝ) = ‖gt‖ ^ 2 := real_inner_self_eq_norm_sq gt
  rw [← h1]
  nth_rewrite 2 [hchar]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have e1 : (⟪gt, g_r⟫ : ℝ) = utility g_r gt := (real_inner_comm gt g_r).symm
  have e2 : (⟪gt, g_f⟫ : ℝ) = utility g_f gt := (real_inner_comm gt g_f).symm
  rw [e1, e2, inv_mul_cancel₀ (ne_of_gt hr), inv_mul_cancel₀ (ne_of_gt hf)]
  norm_num

/-- Lemma 2.8 (Lower bound), `catalog.json`'s `lemma_2_8_lower_bound`. If both gradients are
bounded by `M`, the bargaining coefficients `α_r, α_f` stay at least `1/(√2 M)` away from zero. -/
theorem lemma_2_8_lower_bound (g_r g_f gt : V) (M : ℝ) (_hM : 0 < M)
    (hgr_bound : ‖g_r‖ ≤ M) (hgf_bound : ‖g_f‖ ≤ M)
    (hr : 0 < utility g_r gt) (hf : 0 < utility g_f gt)
    (hchar : gt = (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f) :
    (Real.sqrt 2 * M)⁻¹ ≤ (utility g_r gt)⁻¹ ∧ (Real.sqrt 2 * M)⁻¹ ≤ (utility g_f gt)⁻¹ := by
  have hnormsq : ‖gt‖ ^ 2 = 2 := norm_sq_eq_two g_r g_f gt hr hf hchar
  have hnormgt : ‖gt‖ = Real.sqrt 2 := by
    have : ‖gt‖ = Real.sqrt (‖gt‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg gt)]
    rw [this, hnormsq]
  have hsqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  constructor
  · have hCS : (⟪g_r, gt⟫ : ℝ) ≤ ‖g_r‖ * ‖gt‖ := real_inner_le_norm _ _
    have e1 : (⟪g_r, gt⟫ : ℝ) = utility g_r gt := rfl
    rw [e1, hnormgt] at hCS
    have hub : utility g_r gt ≤ Real.sqrt 2 * M := by
      calc utility g_r gt ≤ ‖g_r‖ * Real.sqrt 2 := hCS
        _ ≤ M * Real.sqrt 2 := mul_le_mul_of_nonneg_right hgr_bound (Real.sqrt_nonneg 2)
        _ = Real.sqrt 2 * M := by ring
    simpa [one_div] using one_div_le_one_div_of_le hr hub
  · have hCS : (⟪g_f, gt⟫ : ℝ) ≤ ‖g_f‖ * ‖gt‖ := real_inner_le_norm _ _
    have e2 : (⟪g_f, gt⟫ : ℝ) = utility g_f gt := rfl
    rw [e2, hnormgt] at hCS
    have hub : utility g_f gt ≤ Real.sqrt 2 * M := by
      calc utility g_f gt ≤ ‖g_f‖ * Real.sqrt 2 := hCS
        _ ≤ M * Real.sqrt 2 := mul_le_mul_of_nonneg_right hgf_bound (Real.sqrt_nonneg 2)
        _ = Real.sqrt 2 * M := by ring
    simpa [one_div] using one_div_le_one_div_of_le hf hub

end Munba
