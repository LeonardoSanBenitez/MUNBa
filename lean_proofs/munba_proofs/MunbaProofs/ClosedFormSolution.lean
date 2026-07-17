import MunbaProofs.SolutionCharacterization

/-!
# Theorem 2.6 (Closed-form solution)

`catalog.json`'s `theorem_2_6_closed_form_solution`. Paper statement: with `K = GᵀG`, `φ` the
angle between `g_r, g_f`, the coefficients from Theorem 2.5's system have the closed form

  `α_r = (1/‖g_r‖) √((1-cos φ)/(sin²φ+ξ))`, `α_f = (1/‖g_f‖) √((1-cos φ)/(sin²φ+ξ))`,

where `ξ` is a small regularization constant added purely for numerical stability near the
degenerate case. We formalize the exact (`ξ = 0`) case, valid whenever `g_r, g_f` are linearly
independent (`sin²φ > 0`) — the degenerate case is Remark 2.7's concern, not this theorem's.

## A genuinely simpler proof than the paper's own

`catalog.json`'s `known_issues_in_paper` flags TWO real gaps in the paper's own derivation route
(quartic elimination → quadratic formula → an informal "we then opt for the sign that keeps
α_f ≥ 0"): (1) the sign selection is asserted, not proved by case analysis; (2) the elimination
divides by `g_2 = ⟪g_r,g_f⟫` without addressing `g_2 = 0`. Both gaps disappear with a different
algebraic route, found while planning this file: multiply Theorem 2.5's two equations through by
`α_r`, `α_f` respectively (no division needed):

  `α_r² g_1 + α_r α_f g_2 = 1`, `α_f² g_3 + α_r α_f g_2 = 1`.

Both right-hand sides equal `1`, so `α_r² g_1 = α_f² g_3` DIRECTLY — no quartic, no `g_2 = 0` case
split, and (since `α_r, α_f > 0` is already known from Theorem 2.3, not something being solved
for) no sign ambiguity either: `α_f/α_r = ‖g_r‖/‖g_f‖` is forced immediately by positivity.
Substituting back into either equation gives `α_r²` directly. This was independently checked
numerically (a non-parallel 2D example) before writing the Lean proof, and it reproduces the
paper's own boxed formula exactly once expressed in `cos φ`/`sin φ` — this file proves the
paper's own stated closed form, just via a route that happens to sidestep both flagged gaps.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The cosine of the angle between `g_r, g_f`, matching the paper's own `cos φ`. -/
noncomputable def cosAngle (g_r g_f : V) : ℝ := ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖)

/-- Theorem 2.6 (Closed-form solution), `catalog.json`'s `theorem_2_6_closed_form_solution`,
exact (`ξ = 0`) case. Given Theorem 2.3's characterization of `gt` and linear independence of
`g_r, g_f` (`sin²φ > 0`), the bargaining coefficients `α_r = (u_r gt)⁻¹`, `α_f = (u_f gt)⁻¹` are
given by the paper's boxed closed form (Eq. 36). -/
theorem theorem_2_6_closed_form_solution (g_r g_f gt : V) (hr0 : g_r ≠ 0) (hf0 : g_f ≠ 0)
    (hr : 0 < utility g_r gt) (hf : 0 < utility g_f gt)
    (hchar : gt = (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f)
    (hsin2 : 0 < 1 - (cosAngle g_r g_f) ^ 2) :
    (utility g_r gt)⁻¹ =
        (1 / ‖g_r‖) * Real.sqrt ((1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2)) ∧
      (utility g_f gt)⁻¹ =
        (1 / ‖g_f‖) * Real.sqrt ((1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2)) := by
  have hnr : (0:ℝ) < ‖g_r‖ := norm_pos_iff.mpr hr0
  have hnf : (0:ℝ) < ‖g_f‖ := norm_pos_iff.mpr hf0
  obtain ⟨heq1, heq2⟩ := theorem_2_5_solution_characterization g_r g_f gt hchar
  set αr : ℝ := (utility g_r gt)⁻¹ with hαr_def
  set αf : ℝ := (utility g_f gt)⁻¹ with hαf_def
  have hαr_pos : 0 < αr := inv_pos.mpr hr
  have hαf_pos : 0 < αf := inv_pos.mpr hf
  -- Multiply Theorem 2.5's two equations through by α_r, α_f (no division): both equal 1.
  have hcancel_r : αr * utility g_r gt = 1 := by rw [hαr_def]; exact inv_mul_cancel₀ (ne_of_gt hr)
  have hcancel_f : αf * utility g_f gt = 1 := by rw [hαf_def]; exact inv_mul_cancel₀ (ne_of_gt hf)
  have hI : αr ^ 2 * ‖g_r‖ ^ 2 + αr * αf * ⟪g_f, g_r⟫ = 1 := by
    have hstep : αr * (αr * ‖g_r‖ ^ 2 + αf * ⟪g_f, g_r⟫) = αr * utility g_r gt := by rw [heq1]
    rw [hcancel_r] at hstep
    nlinarith [hstep]
  have hII : αf ^ 2 * ‖g_f‖ ^ 2 + αr * αf * ⟪g_f, g_r⟫ = 1 := by
    have hstep : αf * (αf * ‖g_f‖ ^ 2 + αr * ⟪g_f, g_r⟫) = αf * utility g_f gt := by rw [heq2]
    rw [hcancel_f] at hstep
    nlinarith [hstep]
  -- Equate: α_r² g_1 = α_f² g_3.
  have hratio_sq : αr ^ 2 * ‖g_r‖ ^ 2 = αf ^ 2 * ‖g_f‖ ^ 2 := by nlinarith [hI, hII]
  -- Positivity forces α_r ‖g_r‖ = α_f ‖g_f‖ (not just up to sign).
  have hratio : αr * ‖g_r‖ = αf * ‖g_f‖ := by
    have h2 : 0 ≤ αr * ‖g_r‖ := mul_nonneg hαr_pos.le hnr.le
    have h3 : 0 ≤ αf * ‖g_f‖ := mul_nonneg hαf_pos.le hnf.le
    nlinarith [hratio_sq, sq_nonneg (αr * ‖g_r‖ - αf * ‖g_f‖), sq_nonneg (αr * ‖g_r‖ + αf * ‖g_f‖)]
  have hαf_eq : αf = αr * ‖g_r‖ / ‖g_f‖ := by
    rw [eq_div_iff (ne_of_gt hnf)]; linarith [hratio]
  have hαr_eq : αr = αf * ‖g_f‖ / ‖g_r‖ := by
    rw [eq_div_iff (ne_of_gt hnr)]; linarith [hratio]
  -- Cauchy-Schwarz gives both ‖g_r‖‖g_f‖ ± ⟪g_f,g_r⟫ ≥ 0.
  have hCS : |(⟪g_f, g_r⟫ : ℝ)| ≤ ‖g_f‖ * ‖g_r‖ := abs_real_inner_le_norm g_f g_r
  have hCS' : -(‖g_r‖ * ‖g_f‖) ≤ ⟪g_f, g_r⟫ ∧ (⟪g_f, g_r⟫ : ℝ) ≤ ‖g_r‖ * ‖g_f‖ := by
    rw [abs_le] at hCS
    constructor <;> nlinarith [hCS.1, hCS.2]
  -- Restate `sin²φ > 0` as a Gram-determinant positivity fact.
  have hsin2' : 0 < ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_f, g_r⟫ ^ 2 := by
    have hc : cosAngle g_r g_f = ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖) := rfl
    have hcomm : (⟪g_r, g_f⟫ : ℝ) = ⟪g_f, g_r⟫ := real_inner_comm g_f g_r
    rw [hc, hcomm, div_pow, sub_pos, div_lt_one (by positivity)] at hsin2
    nlinarith [hsin2, mul_pow ‖g_r‖ ‖g_f‖ 2]
  have hplus_pos : 0 < ‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫ := by
    by_contra hcon
    push Not at hcon
    have heq0 : ‖g_r‖ * ‖g_f‖ = -⟪g_f, g_r⟫ := by linarith [hCS'.1]
    have hsq : (‖g_r‖ * ‖g_f‖) ^ 2 = ⟪g_f, g_r⟫ ^ 2 := by rw [heq0]; ring
    rw [mul_pow] at hsq
    linarith [hsin2', hsq]
  have hminus_pos : 0 < ‖g_r‖ * ‖g_f‖ - ⟪g_f, g_r⟫ := by
    nlinarith [hsin2', hplus_pos, sq_nonneg (‖g_r‖ * ‖g_f‖ - ⟪g_f, g_r⟫)]
  -- Solve for α_r² using the ratio and equation (I).
  have hden_ne : ‖g_r‖ * (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫) ≠ 0 := by positivity
  have hαr_sq : αr ^ 2 = ‖g_f‖ / (‖g_r‖ * (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫)) := by
    rw [hαf_eq] at hI
    rw [eq_div_iff hden_ne]
    field_simp at hI
    linear_combination hI
  -- Relate to the paper's `cos φ` / `sin²φ` notation.
  have hnr_ne : (‖g_r‖ : ℝ) ≠ 0 := ne_of_gt hnr
  have hnf_ne : (‖g_f‖ : ℝ) ≠ 0 := ne_of_gt hnf
  have hplus_ne : (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫ : ℝ) ≠ 0 := ne_of_gt hplus_pos
  have hminus_ne : (‖g_r‖ * ‖g_f‖ - ⟪g_f, g_r⟫ : ℝ) ≠ 0 := ne_of_gt hminus_pos
  have hc_eq : (1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2) =
      ‖g_r‖ * ‖g_f‖ / (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫) := by
    have hden_ne2 : (1 - (cosAngle g_r g_f) ^ 2 : ℝ) ≠ 0 := ne_of_gt hsin2
    rw [div_eq_div_iff hden_ne2 hplus_ne]
    have hc : cosAngle g_r g_f = ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖) := rfl
    have hcomm : (⟪g_r, g_f⟫ : ℝ) = ⟪g_f, g_r⟫ := real_inner_comm g_f g_r
    rw [hc, hcomm]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · have hRHS_nonneg : (0:ℝ) ≤
        (1 / ‖g_r‖) * Real.sqrt ((1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2)) :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hsqrt_arg_nonneg : (0:ℝ) ≤ (1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2) := by
      rw [hc_eq]; positivity
    rw [← sq_eq_sq₀ hαr_pos.le hRHS_nonneg, mul_pow, Real.sq_sqrt hsqrt_arg_nonneg, hαr_sq, hc_eq]
    field_simp
  · have hden_ne2 : ‖g_f‖ * (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫) ≠ 0 := by positivity
    have hαf_sq : αf ^ 2 = ‖g_r‖ / (‖g_f‖ * (‖g_r‖ * ‖g_f‖ + ⟪g_f, g_r⟫)) := by
      rw [hαr_eq] at hII
      rw [eq_div_iff hden_ne2]
      field_simp at hII
      linear_combination hII
    have hRHS_nonneg : (0:ℝ) ≤
        (1 / ‖g_f‖) * Real.sqrt ((1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2)) :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hsqrt_arg_nonneg : (0:ℝ) ≤ (1 - cosAngle g_r g_f) / (1 - (cosAngle g_r g_f) ^ 2) := by
      rw [hc_eq]; positivity
    rw [← sq_eq_sq₀ hαf_pos.le hRHS_nonneg, mul_pow, Real.sq_sqrt hsqrt_arg_nonneg, hαf_sq, hc_eq]
    field_simp

end Munba
