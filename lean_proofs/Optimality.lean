import SphereExtremum
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Theorem 2.3 (Optimality condition)

`catalog.json`'s `theorem_2_3_optimality_condition`. Assembles `NashObjective.lean` and
`SphereExtremum.lean` with Mathlib's Lagrange multiplier theorem
(`Mathlib.Analysis.Calculus.LagrangeMultipliers`) to reach the paper's own conclusion (Eq. 22):
at the optimum, `g̃* = α_r g_r + α_f g_f` for some `α_r, α_f > 0`.

## Bridge-file structure

Three Mathlib facts are specialized here, each named where used:

1. **`hasStrictFDerivAt_norm_sq`** (`Mathlib.Analysis.InnerProductSpace.Calculus`) — the derivative
   of the ball constraint `‖x‖²`.
2. **`HasStrictFDerivAt.log`** (`Mathlib.Analysis.SpecialFunctions.Log.Deriv`) — the chain rule for
   `Real.log` composed with a linear functional, giving the derivative of each `log(u_i(x))` term.
3. **`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`**
   (`Mathlib.Analysis.Calculus.LagrangeMultipliers`) — the Lagrange multiplier theorem itself.

## The `ε = √2` normalization, made explicit

The paper's own proof derives `∇f(g̃*) = λ g̃*` (Eq. 21) then "sets `λ = 1` as a normalization
step" to reach `g̃* = α_r g_r + α_f g_f` (Eq. 22) — phrased as if this were a free choice.
`catalog.json`'s `known_issues_in_paper` already flags that the proof never argues why the ball
constraint even binds (`λ ≠ 0`); working through the argument in full (see `NashObjective.lean`'s
docstring and this file's proof of `theorem_2_3_optimality_condition`) shows something sharper:
`λ = 1/ε²` always (a universal identity, independent of `g_r, g_f`), so Eq. 22 holds as EXACT
equality only when the ball radius is `ε = √2` — never stated explicitly in the paper, but
consistent with (and the real reason behind) `‖g̃*‖² = 2` reappearing as a derived fact in
Lemma 2.8's and Theorem 2.9's own proofs. This file's statement of Theorem 2.3 takes `ε = √2`
as the (paper-implicit) hypothesis, rather than leaving `ε` as an unexplained free parameter.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The Nash objective's derivative at a feasible point `gt`, matching the paper's own
`∇f(g̃*) = g_r/(g_r^T g̃*) + g_f/(g_f^T g̃*)` (Eq. 20), expressed as a continuous linear
functional (`StrongDual ℝ V`) rather than a vector — the Riesz-represented vector is extracted
later, exactly where the main theorem needs it. -/
theorem hasStrictFDerivAt_nashObjective {g_r g_f gt : V} (hgt : gt ∈ feasibleSet g_r g_f) :
    HasStrictFDerivAt (nashObjective g_r g_f)
      ((utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f) gt := by
  obtain ⟨hr, hf⟩ := hgt
  have h1 : HasStrictFDerivAt (fun x => Real.log (utility g_r x))
      ((utility g_r gt)⁻¹ • innerSL ℝ g_r) gt :=
    (innerSL ℝ g_r).hasStrictFDerivAt.log (ne_of_gt hr)
  have h2 : HasStrictFDerivAt (fun x => Real.log (utility g_f x))
      ((utility g_f gt)⁻¹ • innerSL ℝ g_f) gt :=
    (innerSL ℝ g_f).hasStrictFDerivAt.log (ne_of_gt hf)
  exact h1.add h2

/-- Theorem 2.3 (Optimality condition), `catalog.json`'s `theorem_2_3_optimality_condition`.
If `gt` maximizes MUNBa's Nash-bargaining objective over `feasibleSet g_r g_f` intersected with
the ball of radius `√2` (the implicit normalization forced by the paper's Eq. 22, see the module
docstring), then both of the paper's boxed conclusions hold: the optimality condition
`∇f(gt) = gt` (Eq. 21, i.e. `∇f(gt) = λ gt` with `λ = 1` at `ε = √2`), and
`gt = α_r • g_r + α_f • g_f` for `α_r := 1/u_r(gt) > 0`, `α_f := 1/u_f(gt) > 0` (Eq. 22). -/
theorem theorem_2_3_optimality_condition {g_r g_f gt : V}
    (hgt_mem : gt ∈ feasibleSet g_r g_f) (hgt_ball : ‖gt‖ ≤ Real.sqrt 2)
    (hgt_max : ∀ y ∈ feasibleSet g_r g_f, ‖y‖ ≤ Real.sqrt 2 →
      nashObjective g_r g_f y ≤ nashObjective g_r g_f gt) :
    HasGradientAt (nashObjective g_r g_f) gt gt ∧
      gt = (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f ∧
      0 < (utility g_r gt)⁻¹ ∧ 0 < (utility g_f gt)⁻¹ := by
  obtain ⟨hr, hf⟩ := hgt_mem
  -- Step 1 (`NashObjective.lean`): the ball constraint is active.
  have hnorm : ‖gt‖ = Real.sqrt 2 :=
    norm_eq_of_isMax (Real.sqrt_pos.mpr two_pos) ⟨hr, hf⟩ hgt_ball hgt_max
  have hnormsq : ‖gt‖ ^ 2 = 2 := by
    rw [hnorm, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  -- Step 2 (`SphereExtremum.lean`): drop the positivity constraints.
  have hlocalmax : IsLocalMaxOn (nashObjective g_r g_f) {x : V | ‖x‖ = Real.sqrt 2} gt :=
    isLocalMaxOn_sphere_of_isMax ⟨hr, hf⟩ hgt_max
  have hsetEq : {x : V | ‖x‖ = Real.sqrt 2} = {x : V | ‖x‖ ^ 2 = ‖gt‖ ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq, hnormsq]
    constructor
    · intro h; rw [h, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
    · intro h
      have hx0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
      have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith [sq_nonneg (‖x‖ - Real.sqrt 2), sq_nonneg (‖x‖ + Real.sqrt 2)]
  rw [hsetEq] at hlocalmax
  have hextr : IsLocalExtrOn (nashObjective g_r g_f) {x : V | ‖x‖ ^ 2 = ‖gt‖ ^ 2} gt :=
    hlocalmax.isExtr
  -- Step 3: the Lagrange multiplier theorem.
  have hf' : HasStrictFDerivAt (fun x : V => ‖x‖ ^ 2) (2 • innerSL ℝ gt) gt :=
    hasStrictFDerivAt_norm_sq gt
  have hφ' : HasStrictFDerivAt (nashObjective g_r g_f)
      ((utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f) gt :=
    hasStrictFDerivAt_nashObjective ⟨hr, hf⟩
  obtain ⟨a, b, hab, heq⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d hf' hφ'
  -- `b ≠ 0`: else `f' = 0`, forcing `gt = 0`, contradicting feasibility.
  have hgt0 : gt ≠ 0 := ne_zero_of_mem_feasibleSet ⟨hr, hf⟩
  have hbne : b ≠ 0 := by
    intro hb0
    have ha0 : a ≠ 0 := by
      intro ha0; apply hab; simp [ha0, hb0]
    have hfz : a • (2 • innerSL ℝ gt) + b • ((utility g_r gt)⁻¹ • innerSL ℝ g_r +
        (utility g_f gt)⁻¹ • innerSL ℝ g_f) = 0 := heq
    rw [hb0, zero_smul, add_zero] at hfz
    have hrw : a • (2 • innerSL ℝ gt) = (2 * a) • innerSL ℝ gt := by module
    rw [hrw] at hfz
    have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha0
    have := (smul_eq_zero.mp hfz).resolve_left h2a
    have hgt_eq_zero : gt = 0 := by
      have hval := ContinuousLinearMap.ext_iff.mp this gt
      simp only [innerSL_apply_apply, zero_apply] at hval
      exact inner_self_eq_zero.mp hval
    exact hgt0 hgt_eq_zero
  -- Extract `μ := -2a/b` with `φ' = μ • innerSL ℝ gt`.
  set μ : ℝ := -(2 * a) / b with hμ_def
  have hφ'_eq : (utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f
      = μ • innerSL ℝ gt := by
    have hfz : a • (2 • innerSL ℝ gt) + b • ((utility g_r gt)⁻¹ • innerSL ℝ g_r +
        (utility g_f gt)⁻¹ • innerSL ℝ g_f) = 0 := heq
    have hfz' : b • ((utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f) +
        a • (2 • innerSL ℝ gt) = 0 := by rw [add_comm]; exact hfz
    have hsmul : b • ((utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f)
        = -(a • (2 • innerSL ℝ gt)) := eq_neg_of_add_eq_zero_left hfz'
    have hkey : (utility g_r gt)⁻¹ • innerSL ℝ g_r + (utility g_f gt)⁻¹ • innerSL ℝ g_f
        = b⁻¹ • (-(a • (2 • innerSL ℝ gt))) := by
      rw [← hsmul, smul_smul, inv_mul_cancel₀ hbne, one_smul]
    rw [hkey, hμ_def]
    module
  -- Evaluate both descriptions of `φ'` at `gt` itself: universally `= 2`; via `μ`, `= 2μ`.
  have heval1 : ((utility g_r gt)⁻¹ • innerSL ℝ g_r +
      (utility g_f gt)⁻¹ • innerSL ℝ g_f) gt = 2 := by
    have e1 : (innerSL ℝ g_r : V →L[ℝ] ℝ) gt = utility g_r gt := rfl
    have e2 : (innerSL ℝ g_f : V →L[ℝ] ℝ) gt = utility g_f gt := rfl
    simp only [add_apply, smul_apply, smul_eq_mul, e1, e2]
    rw [inv_mul_cancel₀ (ne_of_gt hr), inv_mul_cancel₀ (ne_of_gt hf)]
    norm_num
  have heval2 : (μ • innerSL ℝ gt : V →L[ℝ] ℝ) gt = μ * 2 := by
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq, hnormsq]
  rw [hφ'_eq, heval2] at heval1
  have hμ1 : μ = 1 := by linarith
  rw [hμ1, one_smul] at hφ'_eq
  -- Riesz uniqueness: `⟪target, v⟫ = ⟪gt, v⟫` for all `v` implies `target = gt`.
  have hriesz : ∀ v : V,
      (⟪(utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f, v⟫ : ℝ) = ⟪gt, v⟫ := by
    intro v
    have hval := ContinuousLinearMap.ext_iff.mp hφ'_eq v
    simpa [innerSL_apply_apply, inner_add_left, real_inner_smul_left] using hval
  have hfinal : (utility g_r gt)⁻¹ • g_r + (utility g_f gt)⁻¹ • g_f = gt :=
    ext_inner_right ℝ hriesz
  -- Eq. 21: `∇f(gt) = gt` (i.e. `∇f(gt) = λ gt` with `λ = 1`, the `ε = √2` normalization).
  have hgrad_gt : HasGradientAt (nashObjective g_r g_f) gt gt := by
    have hfderiv : HasFDerivAt (nashObjective g_r g_f) (innerSL ℝ gt) gt := by
      have h := hφ'.hasFDerivAt
      rwa [hφ'_eq] at h
    have hdual : (innerSL ℝ gt : V →L[ℝ] ℝ) = InnerProductSpace.toDual ℝ V gt := by
      ext v
      simp [innerSL_apply_apply, InnerProductSpace.toDual_apply_apply]
    rw [hdual] at hfderiv
    exact hfderiv
  exact ⟨hgrad_gt, hfinal.symm, inv_pos.mpr hr, inv_pos.mpr hf⟩

end Munba
