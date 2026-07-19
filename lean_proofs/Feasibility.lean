import Basic

/-!
# Lemma 2.1 (Feasibility)

`catalog.json`'s `lemma_2_1_feasibility`. Paper statement: if the cosine similarity of `g_r, g_f`
is strictly between `-1` and `0`, the feasible set `C = {g̃ | u_r(g̃) > 0 ∧ u_f(g̃) > 0}` is
non-empty.

## Proof route (a single-witness variant)

The paper parametrizes the whole segment `g̃ = α•ĝ_r + (1-α)•ĝ_f` (`ĝ` = normalized) and solves
for a range of valid `α ∈ [0,1]` (Eqs. 9-13). We instead exhibit directly the SINGLE witness
`g̃ := ‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f` (the paper's own witness at `α = 1/2`, i.e. the midpoint of
the two normalized gradients). A direct computation gives

  `⟪g_r, g̃⟫ = ‖g_r‖ * (1 + c)` and, symmetrically, `⟪g_f, g̃⟫ = ‖g_f‖ * (1 + c)`,

where `c := ⟪g_r,g_f⟫ / (‖g_r‖ * ‖g_f‖)` is the cosine similarity. Both are positive under the
WEAKER hypothesis `c > -1` alone — the paper's upper bound `c < 0` is not needed for existence
(only for other parts of MUNBa's motivation/argument, presumably). This still proves exactly the
paper's stated lemma, since `-1 < c < 0` implies `c > -1`; documented here explicitly so a reader
comparing against the paper's Eqs. (9)-(13) is not confused by how different the Lean proof looks.
-/

open scoped RealInnerProductSpace

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Lemma 2.1 (Feasibility), `catalog.json`'s `lemma_2_1_feasibility`. -/
theorem lemma_2_1_feasibility (g_r g_f : V) (hr : g_r ≠ 0) (hf : g_f ≠ 0)
    (hc_lb : -1 < ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖))
    (_hc_ub : ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖) < 0) :
    (feasibleSet g_r g_f).Nonempty := by
  have hnr : (0 : ℝ) < ‖g_r‖ := norm_pos_iff.mpr hr
  have hnf : (0 : ℝ) < ‖g_f‖ := norm_pos_iff.mpr hf
  set c : ℝ := ⟪g_r, g_f⟫ / (‖g_r‖ * ‖g_f‖) with hc_def
  have hc1 : (0:ℝ) < 1 + c := by linarith
  refine ⟨‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f, ?_, ?_⟩
  · show (0:ℝ) < utility g_r (‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f)
    have key : utility g_r (‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f) = ‖g_r‖ * (1 + c) := by
      change ⟪g_r, ‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f⟫ = ‖g_r‖ * (1 + c)
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      rw [hc_def]
      field_simp
    rw [key]
    exact mul_pos hnr hc1
  · show (0:ℝ) < utility g_f (‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f)
    have key : utility g_f (‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f) = ‖g_f‖ * (1 + c) := by
      change ⟪g_f, ‖g_r‖⁻¹ • g_r + ‖g_f‖⁻¹ • g_f⟫ = ‖g_f‖ * (1 + c)
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, real_inner_comm g_r g_f]
      rw [hc_def]
      field_simp
      ring
    rw [key]
    exact mul_pos hnf hc1

end Munba
