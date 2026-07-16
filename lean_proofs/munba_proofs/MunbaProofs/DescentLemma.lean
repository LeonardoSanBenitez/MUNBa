import MunbaProofs.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Lemma 6.1 (Lipschitz-smoothness descent lemma)

`catalog.json`'s `lemma_6_1_descent_lemma`. Standard "descent lemma" from convex optimization: if
a function's gradient is Lipschitz, the function is upper-bounded by its own first-order Taylor
expansion plus a quadratic penalty term.

## This is a bridge file, not a from-scratch proof

The mathematical content here is completely standard and already available in Mathlib in
general form — the goal of this file is NOT to reprove it, but to state MUNBa's own Lemma 6.1,
in the paper's own notation, and show explicitly how it follows from the general machinery. This
matters because the point of formalizing MUNBa is to give a reader of the *paper* mechanically
checked confidence that its claims hold, and to leave behind an explicit, legible bridge between
the paper's specific statement and the general library fact that future work (on MUNBa itself, or
on results that build on it) can reuse directly.

The two general facts being specialized here:

1. **`HasGradientAt`** (`Mathlib.Analysis.Calculus.Gradient.Basic`) — Mathlib's
   Riesz-representation-aware notion of "the gradient of `𝓛` at `θ` is the vector `g`," i.e.
   exactly the paper's own `∇𝓛(θ)`, avoiding manual conversion between a continuous linear
   functional and its representing vector.
2. **`image_le_of_deriv_right_le_deriv_boundary`** (`Mathlib.Analysis.Calculus.MeanValue`) — a
   general real-valued "fencing" comparison theorem: if `f, B : ℝ → ℝ` are continuous on `[a, b]`,
   `f a ≤ B a`, and `f' t ≤ B' t` pointwise on `[a, b)`, then `f x ≤ B x` on all of `[a, b]`. This
   directly replaces the paper's own Taylor-expansion-with-integral-remainder argument (Eq. 40):
   instead of integrating a derivative bound by hand, we exhibit a quadratic "boundary" function
   `B` matching the target bound and let this general theorem do the integration.

## Notational note

The paper uses the SAME symbol `L` both for the loss function (rendered `\mathcal{L}` /
calligraphic-`L` in the typeset paper) and for the Lipschitz constant of its gradient —
`catalog.json`'s `known_issues_in_paper` for this item flags this explicitly ("both rendered as
'L' in plain text/ASCII"). We disambiguate as `𝓛` (the loss function) and `Lconst` (the Lipschitz
constant), preserving the paper's own two distinct MEANINGS even though the paper does not
distinguish the two SYMBOLS.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The segment from `θ` to `θ'`, parametrized by `t ∈ [0,1]`, always has the constant velocity
`θ' - θ`. Named to match the paper's implicit use of `θ + t(θ'-θ)` in Eq. (40)'s proof. -/
theorem hasDerivAt_segment (θ v : V) (t : ℝ) :
    HasDerivAt (fun t : ℝ => θ + t • v) v t := by
  have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  simpa using h1.const_add θ

/-- Lemma 6.1 (the Lipschitz-smoothness descent lemma), `catalog.json`'s
`lemma_6_1_descent_lemma`. If `𝓛`'s gradient `g` is `Lconst`-Lipschitz, `𝓛` is upper-bounded by
its first-order Taylor expansion around `θ` plus a quadratic penalty — the paper's boxed Eq. (40).
-/
theorem lemma_6_1_descent_lemma (𝓛 : V → ℝ) (g : V → V) (Lconst : ℝ)
    (hgrad : ∀ θ, HasGradientAt 𝓛 (g θ) θ)
    (hLip : ∀ θ₁ θ₂, ‖g θ₁ - g θ₂‖ ≤ Lconst * ‖θ₁ - θ₂‖)
    (θ θ' : V) :
    𝓛 θ' ≤ 𝓛 θ + ⟪g θ, θ' - θ⟫ + (Lconst / 2) * ‖θ' - θ‖ ^ 2 := by
  set v : V := θ' - θ with hv_def
  -- `f t = 𝓛 (θ + t•v)`: the paper's `𝓛(θ + t(θ'-θ))` restricted to the segment `t ∈ [0,1]`.
  set f : ℝ → ℝ := fun t => 𝓛 (θ + t • v) with hf_def
  -- `B t`: the comparison/"boundary" function. `B 1` is exactly the RHS of the paper's Eq. (40).
  set B : ℝ → ℝ := fun t => 𝓛 θ + t * ⟪g θ, v⟫ + Lconst / 2 * t ^ 2 * ‖v‖ ^ 2 with hB_def
  have hf0 : f 0 = B 0 := by simp [hf_def, hB_def]
  have hfderiv : ∀ t : ℝ, HasDerivAt f (⟪g (θ + t • v), v⟫) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => θ + t • v) v t := hasDerivAt_segment θ v t
    have hgrad' : HasFDerivAt 𝓛 (InnerProductSpace.toDual ℝ V (g (θ + t • v))) (θ + t • v) :=
      (hgrad (θ + t • v)).hasFDerivAt
    have hcomp := hgrad'.comp_hasDerivAt t hcurve
    have hval : (InnerProductSpace.toDual ℝ V (g (θ + t • v))) v = ⟪g (θ + t • v), v⟫ :=
      InnerProductSpace.toDual_apply_apply
    rw [hval] at hcomp
    exact hcomp
  have hBderiv : ∀ t : ℝ, HasDerivAt B (⟪g θ, v⟫ + Lconst * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t * ⟪g θ, v⟫) (⟪g θ, v⟫) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪g θ, v⟫)
    have h2 : HasDerivAt (fun t : ℝ => Lconst / 2 * t ^ 2 * ‖v‖ ^ 2) (Lconst * t * ‖v‖ ^ 2) t := by
      have h2a : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h2b := (h2a.const_mul (Lconst / 2)).mul_const (‖v‖ ^ 2)
      have heq : Lconst / 2 * (2 * t) * ‖v‖ ^ 2 = Lconst * t * ‖v‖ ^ 2 := by ring
      rwa [heq] at h2b
    have h3 := (h1.const_add (𝓛 θ)).add h2
    exact h3
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      (⟪g (θ + t • v), v⟫ : ℝ) ≤ ⟪g θ, v⟫ + Lconst * t * ‖v‖ ^ 2 := by
    intro t ht
    have ht_nonneg : (0:ℝ) ≤ t := ht.1
    have hCS : (⟪g (θ + t • v) - g θ, v⟫ : ℝ) ≤ ‖g (θ + t • v) - g θ‖ * ‖v‖ :=
      real_inner_le_norm _ _
    have hLipT : ‖g (θ + t • v) - g θ‖ ≤ Lconst * ‖t • v‖ := by
      have := hLip (θ + t • v) θ
      simpa using this
    have hnorm_tv : ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
    have key : (⟪g (θ + t • v) - g θ, v⟫ : ℝ) ≤ Lconst * t * ‖v‖ ^ 2 := by
      calc (⟪g (θ + t • v) - g θ, v⟫ : ℝ) ≤ ‖g (θ + t • v) - g θ‖ * ‖v‖ := hCS
        _ ≤ (Lconst * ‖t • v‖) * ‖v‖ := by
              have hv0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
              exact mul_le_mul_of_nonneg_right hLipT hv0
        _ = Lconst * (|t| * ‖v‖) * ‖v‖ := by rw [hnorm_tv]
        _ = Lconst * t * ‖v‖ ^ 2 := by
              rw [abs_of_nonneg ht_nonneg]
              ring
    have hsplit : (⟪g (θ + t • v), v⟫ : ℝ) = ⟪g (θ + t • v) - g θ, v⟫ + ⟪g θ, v⟫ := by
      rw [inner_sub_left]; ring
    rw [hsplit]
    linarith [key]
  have hfC : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    fun t _ => (hfderiv t).continuousAt.continuousWithinAt
  have hBC : ContinuousOn B (Set.Icc (0:ℝ) 1) :=
    fun t _ => (hBderiv t).continuousAt.continuousWithinAt
  have hmain := image_le_of_deriv_right_le_deriv_boundary hfC
    (fun t _ => (hfderiv t).hasDerivWithinAt) hf0.le hBC
    (fun t _ => (hBderiv t).hasDerivWithinAt) hbound (Set.right_mem_Icc.mpr zero_le_one)
  have hf1 : f 1 = 𝓛 θ' := by
    simp [hf_def, hv_def]
  have hB1 : B 1 = 𝓛 θ + ⟪g θ, θ' - θ⟫ + Lconst / 2 * ‖θ' - θ‖ ^ 2 := by
    simp [hB_def, hv_def]
  rw [hf1, hB1] at hmain
  linarith [hmain]

end Munba
