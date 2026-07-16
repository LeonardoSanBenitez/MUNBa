import MunbaProofs.Basic

/-!
# Lemma 2.2 (Cone property)

`catalog.json`'s `lemma_2_2_cone_property`. Paper statement: the feasible set `C` from Lemma 2.1
is closed under multiplication by positive scalars.

`catalog.json`'s own `known_issues_in_paper` for this item notes the statement is really an
instance of a fully general fact ("the positivity region of ANY pair of functions that are
positively homogeneous of degree 1 is a cone"), not anything specific to `u_r,u_f` being built
from gradients. We record that general fact first (`cone_of_pos_homogeneous`, phrased with plain
homogeneity hypotheses rather than bundled `LinearMap`s — equivalent generality for this remark,
less boilerplate), then derive Lemma 2.2 itself as a corollary.
-/

open scoped RealInnerProductSpace

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- General fact (not literally in the paper, but the actual content behind Lemma 2.2 per
`catalog.json`'s `known_issues_in_paper`): the positivity region of a pair of functions that are
each positively homogeneous of degree 1 is closed under multiplication by a positive scalar. -/
theorem cone_of_pos_homogeneous {φ ψ : V → ℝ}
    (hφ : ∀ r : ℝ, 0 < r → ∀ x, φ (r • x) = r * φ x)
    (hψ : ∀ r : ℝ, 0 < r → ∀ x, ψ (r • x) = r * ψ x)
    {gt : V} (h : 0 < φ gt ∧ 0 < ψ gt) {β : ℝ} (hβ : 0 < β) :
    0 < φ (β • gt) ∧ 0 < ψ (β • gt) := by
  rw [hφ β hβ gt, hψ β hβ gt]
  exact ⟨mul_pos hβ h.1, mul_pos hβ h.2⟩

/-- `utility g` is positively homogeneous of degree 1 in its second argument, for any fixed `g` —
the instantiation of `cone_of_pos_homogeneous`'s hypothesis needed for Lemma 2.2. -/
theorem utility_pos_homogeneous (g : V) (r : ℝ) (_hr : 0 < r) (x : V) :
    utility g (r • x) = r * utility g x := by
  change ⟪g, r • x⟫ = r * ⟪g, x⟫
  rw [real_inner_smul_right]

/-- Lemma 2.2 (Cone property), `catalog.json`'s `lemma_2_2_cone_property`. -/
theorem lemma_2_2_cone_property (g1 g2 : V) {gt : V} (hgt : gt ∈ feasibleSet g1 g2)
    {β : ℝ} (hβ : 0 < β) : β • gt ∈ feasibleSet g1 g2 :=
  cone_of_pos_homogeneous (utility_pos_homogeneous g1) (utility_pos_homogeneous g2) hgt hβ

end Munba
