import MunbaProofs.LowerBound
import MunbaProofs.DescentLemma

/-!
# Theorem 2.9 (Pareto improvement)

`catalog.json`'s `theorem_2_9_pareto_improvement`. Paper statement: with the MUNBa update
`θ^(t+1) = θ^(t) - η^(t) g̃^(t)` and a learning rate capped by `η^(t) = min_i 1/(L α_i^(t))`,
neither player's loss increases at any single step.

## Structure: a single-player descent step, applied to both players

The paper's proof is symmetric in `r, f` — the same computation, once per player, using only that
player's own `α_i` and gradient. This file factors that out as `single_player_descent_step` (any
one player's loss doesn't increase, given only ITS OWN Lipschitz-smoothness, its own bargaining
coefficient, and the shared learning-rate cap), then assembles Theorem 2.9 itself as two
applications of it. Reuses `MunbaProofs.DescentLemma`'s Lemma 6.1 (the descent inequality) and
`MunbaProofs.LowerBound`'s `norm_sq_eq_two` (`‖g̃*‖²=2`, Eq. 41 in the paper — the same identity
Lemma 2.8 needs, not duplicated).
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- One player's step of Theorem 2.9's argument: if `𝓛`'s gradient is `Lconst`-Lipschitz
(`Lconst > 0`), `α := 1/⟪g θ, gt⟫ > 0` is that player's bargaining coefficient, `‖gt‖² = 2`
(Eq. 41), and the learning rate `η` is positive and capped by `1/(Lconst·α)`, then a single MUNBa
step along `-gt` does not increase this player's loss. -/
theorem single_player_descent_step (𝓛 : V → ℝ) (g : V → V)
    (θ gt : V) (Lc α₀ η₀ : ℝ)
    (hgrad : ∀ θ, HasGradientAt 𝓛 (g θ) θ)
    (hLip : ∀ θ₁ θ₂, ‖g θ₁ - g θ₂‖ ≤ Lc * ‖θ₁ - θ₂‖)
    (hgt2 : ‖gt‖ ^ 2 = 2) (hu : utility (g θ) gt = α₀⁻¹) (_hα_pos : 0 < α₀)
    (hLc_pos : 0 < Lc) (hη_pos : 0 < η₀) (hη : η₀ ≤ (Lc * α₀)⁻¹) :
    𝓛 (θ - η₀ • gt) ≤ 𝓛 θ := by
  have hdescent := lemma_6_1_descent_lemma 𝓛 g Lc hgrad hLip θ (θ - η₀ • gt)
  have hv : θ - η₀ • gt - θ = -(η₀ • gt) := by abel
  rw [hv] at hdescent
  have hinner : (⟪g θ, -(η₀ • gt)⟫ : ℝ) = -(η₀ * (utility (g θ) gt)) := by
    rw [inner_neg_right, real_inner_smul_right]
    congr 1
  have hnorm : ‖(-(η₀ • gt) : V)‖ ^ 2 = η₀ ^ 2 * 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hgt2]
  rw [hinner, hnorm, hu] at hdescent
  have hkey : 𝓛 θ - η₀ * α₀⁻¹ + Lc / 2 * (η₀ ^ 2 * 2) ≤ 𝓛 θ := by
    have hstep : Lc * η₀ ≤ α₀⁻¹ := by
      have h1 : Lc * η₀ ≤ Lc * (Lc * α₀)⁻¹ := mul_le_mul_of_nonneg_left hη hLc_pos.le
      have h2 : Lc * (Lc * α₀)⁻¹ = α₀⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hLc_pos), one_mul]
      rwa [h2] at h1
    nlinarith [mul_le_mul_of_nonneg_left hstep hη_pos.le]
  linarith [hdescent, hkey]

/-- Theorem 2.9 (Pareto improvement), `catalog.json`'s `theorem_2_9_pareto_improvement`. With the
MUNBa update along `g̃* = α_r g_r + α_f g_f` and learning rate `η ≤ min(1/(L α_r), 1/(L α_f))`,
neither player's loss increases. -/
theorem theorem_2_9_pareto_improvement (𝓛_r 𝓛_f : V → ℝ) (g_r g_f : V → V) (Lc : ℝ)
    (hgrad_r : ∀ θ, HasGradientAt 𝓛_r (g_r θ) θ)
    (hgrad_f : ∀ θ, HasGradientAt 𝓛_f (g_f θ) θ)
    (hLip_r : ∀ θ₁ θ₂, ‖g_r θ₁ - g_r θ₂‖ ≤ Lc * ‖θ₁ - θ₂‖)
    (hLip_f : ∀ θ₁ θ₂, ‖g_f θ₁ - g_f θ₂‖ ≤ Lc * ‖θ₁ - θ₂‖)
    (hLc_pos : 0 < Lc) (θ gt : V)
    (hr : 0 < utility (g_r θ) gt) (hf : 0 < utility (g_f θ) gt)
    (hchar : gt = (utility (g_r θ) gt)⁻¹ • g_r θ + (utility (g_f θ) gt)⁻¹ • g_f θ)
    (η : ℝ) (hη_pos : 0 < η)
    (hη_r : η ≤ (Lc * (utility (g_r θ) gt)⁻¹)⁻¹) (hη_f : η ≤ (Lc * (utility (g_f θ) gt)⁻¹)⁻¹) :
    𝓛_r (θ - η • gt) ≤ 𝓛_r θ ∧ 𝓛_f (θ - η • gt) ≤ 𝓛_f θ := by
  have hgt2 : ‖gt‖ ^ 2 = 2 := norm_sq_eq_two (g_r θ) (g_f θ) gt hr hf hchar
  have hur : utility (g_r θ) gt = ((utility (g_r θ) gt)⁻¹)⁻¹ := (inv_inv _).symm
  have huf : utility (g_f θ) gt = ((utility (g_f θ) gt)⁻¹)⁻¹ := (inv_inv _).symm
  refine ⟨?_, ?_⟩
  · exact single_player_descent_step 𝓛_r g_r θ gt Lc (utility (g_r θ) gt)⁻¹ η
      hgrad_r hLip_r hgt2 hur (inv_pos.mpr hr) hLc_pos hη_pos hη_r
  · exact single_player_descent_step 𝓛_f g_f θ gt Lc (utility (g_f θ) gt)⁻¹ η
      hgrad_f hLip_f hgt2 huf (inv_pos.mpr hf) hLc_pos hη_pos hη_f

end Munba
