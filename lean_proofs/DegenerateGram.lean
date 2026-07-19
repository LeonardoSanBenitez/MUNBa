import Basic

/-!
# Remark 2.7 (degenerate/aligned-gradient case)

`catalog.json`'s `remark_2_7_degenerate_gram_matrix`. The remark's content: if `g_r, g_f` are
linearly dependent (`g_r = ζ g_f` for some scalar `ζ`), the Gram matrix `K = GᵀG` becomes
singular (`det K = 0`).

## Scope

`catalog.json`'s `known_issues_in_paper` for this item is explicit: "only the FIRST claim ...
is an actual provable mathematical statement -- and an easy one (a Gram matrix of two linearly
dependent vectors is always rank ≤ 1, hence singular; standard linear algebra, essentially the
Cauchy-Schwarz equality case)." The rest of the remark (noise-injection for `ζ < 0`, the
`α = [0.5, 0.5]` convention for `ζ ≥ 0`) is engineering heuristic, not a mathematical claim, and
is explicitly out of scope for this formalization (nothing to prove there).
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Remark 2.7's provable content, `catalog.json`'s `remark_2_7_degenerate_gram_matrix`: if
`g_r, g_f` are linearly dependent, the Gram matrix `K`'s determinant `‖g_r‖²‖g_f‖² - ⟪g_r,g_f⟫²`
vanishes. -/
theorem remark_2_7_degenerate_gram_matrix (g_r g_f : V) (ζ : ℝ) (hdep : g_r = ζ • g_f) :
    ‖g_r‖ ^ 2 * ‖g_f‖ ^ 2 - ⟪g_r, g_f⟫ ^ 2 = 0 := by
  have hnorm : ‖g_r‖ ^ 2 = ζ ^ 2 * ‖g_f‖ ^ 2 := by
    rw [hdep, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hinner : (⟪g_r, g_f⟫ : ℝ) = ζ * ‖g_f‖ ^ 2 := by
    rw [hdep, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hnorm, hinner]
  ring

end Munba
