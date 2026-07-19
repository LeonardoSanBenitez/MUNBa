import Basic

/-!
# Lemma 2.4 (Linear dependence)

`catalog.json`'s `lemma_2_4_linear_dependence`. Paper statement: at a Pareto stationary point,
`g_r` and `g_f` are linearly dependent. The paper's own proof imports an external "first-order
optimality condition for Pareto optimality" (citing Ye & Liu, UAI 2022, and Roy–So–Ma,
arXiv:2308.02145) and never itself defines "Pareto stationary point."

## What "Pareto stationary" means here, and why this route

A standard, textbook reading of "Pareto stationary" for two objectives being minimized: there is
no direction `d` that is a strict descent direction for BOTH objectives simultaneously — formally,
`∀ d, ¬(⟪g_r,d⟫ < 0 ∧ ⟪g_f,d⟫ < 0)`. The claim "this implies `g_r, g_f` linearly dependent" is a
two-vector instance of **Gordan's theorem of the alternative**, a classical (100+ year old) fact
in convex analysis, not a modern open research question — even though the specific term "Pareto
stationarity" doesn't appear formalized under that name in any mainstream proof assistant (true,
but a different and much weaker claim than "the underlying mathematics is inaccessible").

Mathlib has real convex-cone duality machinery for the general case
(`Mathlib.Analysis.Convex.Cone.InnerDual`: `ProperCone.hyperplane_separation'`, the geometric form
of Farkas' lemma, and `ProperCone.innerDual_innerDual`, the bipolar theorem). For exactly TWO
vectors, though, it is simpler and more legible to prove the needed direction directly and
constructively, by contraposition: if `g_r, g_f` are linearly INDEPENDENT (Gram determinant
`‖g_r‖²‖g_f‖² - ⟪g_r,g_f⟫² > 0`), solve the 2×2 Gram system for `a, b` with
`a‖g_r‖² + b⟪g_r,g_f⟫ = 1` and `a⟪g_r,g_f⟫ + b‖g_f‖² = 1` (via Cramer's rule — solvable exactly
because the Gram determinant is nonzero), and `d := -(a•g_r + b•g_f)` is then an EXPLICIT common
strict descent direction: `⟪g_r,d⟫ = ⟪g_f,d⟫ = -1 < 0`. Contraposing gives Lemma 2.4.

This file also provides the elementary helper `gr_linearlyDependent_of_combination_eq_zero`
(if a positive combination `α_r•g_r+α_f•g_f` vanishes, then `g_r, g_f` are dependent), which
Theorem 2.10's closing argument reuses.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Constructive core of Gordan's alternative for two vectors: if `g_r, g_f` are linearly
independent (positive Gram determinant), there is an explicit common strict descent direction. -/
theorem exists_common_descent_direction_of_gram_det_pos {g_r g_f : V}
    (hD : 0 < ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_r, g_f⟫ ^ 2) :
    ∃ d : V, ⟪g_r, d⟫ < 0 ∧ ⟪g_f, d⟫ < 0 := by
  set D : ℝ := ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_r, g_f⟫ ^ 2 with hD_def
  set a : ℝ := (‖g_f‖ ^ 2 - ⟪g_r, g_f⟫) / D with ha_def
  set b : ℝ := (‖g_r‖ ^ 2 - ⟪g_r, g_f⟫) / D with hb_def
  refine ⟨-(a • g_r + b • g_f), ?_, ?_⟩
  · have hcomp : (⟪g_r, -(a • g_r + b • g_f)⟫ : ℝ) = -(a * ‖g_r‖ ^ 2 + b * ⟪g_r, g_f⟫) := by
      rw [inner_neg_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
    rw [hcomp, ha_def, hb_def]
    have hnum : (‖g_f‖ ^ 2 - ⟪g_r, g_f⟫) * ‖g_r‖ ^ 2 +
        (‖g_r‖ ^ 2 - ⟪g_r, g_f⟫) * ⟪g_r, g_f⟫ = D := by rw [hD_def]; ring
    have : (‖g_f‖ ^ 2 - ⟪g_r, g_f⟫) / D * ‖g_r‖ ^ 2 +
        (‖g_r‖ ^ 2 - ⟪g_r, g_f⟫) / D * ⟪g_r, g_f⟫ = 1 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum, div_self (ne_of_gt hD)]
    rw [this]; norm_num
  · have hcomp : (⟪g_f, -(a • g_r + b • g_f)⟫ : ℝ) = -(a * ⟪g_r, g_f⟫ + b * ‖g_f‖ ^ 2) := by
      rw [inner_neg_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, real_inner_comm g_f g_r]
    rw [hcomp, ha_def, hb_def]
    have hnum : (‖g_f‖ ^ 2 - ⟪g_r, g_f⟫) * ⟪g_r, g_f⟫ +
        (‖g_r‖ ^ 2 - ⟪g_r, g_f⟫) * ‖g_f‖ ^ 2 = D := by rw [hD_def]; ring
    have : (‖g_f‖ ^ 2 - ⟪g_r, g_f⟫) / D * ⟪g_r, g_f⟫ +
        (‖g_r‖ ^ 2 - ⟪g_r, g_f⟫) / D * ‖g_f‖ ^ 2 = 1 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum, div_self (ne_of_gt hD)]
    rw [this]; norm_num

/-- Lemma 2.4 (Linear dependence), `catalog.json`'s `lemma_2_4_linear_dependence`: at a Pareto
stationary point (no common strict descent direction for `g_r, g_f`), the Gram determinant
vanishes — i.e. `g_r, g_f` are linearly dependent (the same characterization Remark 2.7 uses,
`DegenerateGram.lean`). Proved by contraposing
`exists_common_descent_direction_of_gram_det_pos`. -/
theorem lemma_2_4_linear_dependence {g_r g_f : V}
    (hstationary : ∀ d : V, ¬(⟪g_r, d⟫ < 0 ∧ ⟪g_f, d⟫ < 0)) :
    ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_r, g_f⟫ ^ 2 = 0 := by
  by_contra hne
  have hCS : |(⟪g_r, g_f⟫ : ℝ)| ≤ ‖g_r‖ * ‖g_f‖ := abs_real_inner_le_norm g_r g_f
  have hD_nonneg : 0 ≤ ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_r, g_f⟫ ^ 2 := by
    nlinarith [abs_le.mp hCS, sq_abs (⟪g_r, g_f⟫ : ℝ)]
  obtain ⟨d, hd1, hd2⟩ := exists_common_descent_direction_of_gram_det_pos
    (lt_of_le_of_ne hD_nonneg (Ne.symm hne))
  exact hstationary d ⟨hd1, hd2⟩

/-- The elementary fact also used by Theorem 2.10's closing argument: if a positive combination
`α_r • g_r + α_f • g_f` vanishes, `g_r` is an explicit scalar multiple of `g_f`. -/
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

end Munba
