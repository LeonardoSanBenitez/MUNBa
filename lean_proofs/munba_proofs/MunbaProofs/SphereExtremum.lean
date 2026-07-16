import MunbaProofs.NashObjective
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.LocalExtr

/-!
# Building block for Theorem 2.3: dropping the two positivity constraints

`catalog.json`'s `theorem_2_3_optimality_condition`. Second building block (after
`NashObjective.lean`'s "the ball constraint is active" argument): the paper's Theorem 2.3 sets up
a 3-constraint optimization (one ball constraint, two strict-positivity constraints), but since
`gt ∈ feasibleSet g_r g_f` means the positivity constraints are open/strict, they can never be
BINDING at a feasible point — a genuinely simpler reason than the paper's own "complementary
slackness" argument (Eq. 19), which needed the KKT multipliers `ζ_r, ζ_f` to conclude they vanish.
Here we show directly that a maximizer over `ball ∩ feasibleSet` is already a local extremum of
the objective on the SPHERE alone (dropping `feasibleSet` from the constraint set entirely) — the
exact hypothesis shape Mathlib's Lagrange multiplier theorem needs
(`IsLocalExtrOn φ {x | f x = f x₀} x₀`, a single equality constraint).
-/

namespace Munba

open scoped RealInnerProductSpace
open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `feasibleSet g_r g_f` is open: both `utility g_r`, `utility g_f` are continuous (they are
inner products with a fixed vector), so the feasible set is an intersection of two preimages of
the open ray `(0, ∞)`. -/
theorem isOpen_feasibleSet (g_r g_f : V) : IsOpen (feasibleSet g_r g_f) := by
  have h1 : Continuous (utility g_r) := continuous_const.inner continuous_id
  have h2 : Continuous (utility g_f) := continuous_const.inner continuous_id
  have heq : feasibleSet g_r g_f = utility g_r ⁻¹' Set.Ioi 0 ∩ utility g_f ⁻¹' Set.Ioi 0 := rfl
  rw [heq]
  exact (isOpen_Ioi.preimage h1).inter (isOpen_Ioi.preimage h2)

/-- **Dropping the positivity constraints**: if `gt` maximizes MUNBa's objective over
`feasibleSet g_r g_f` intersected with the ball of radius `ε`, then `gt` is already a local
extremum of the objective on the SPHERE of radius `ε` alone — the two positivity constraints can
be dropped entirely, since `feasibleSet g_r g_f` (being open) is automatically satisfied on a
whole neighborhood of `gt`. -/
theorem isLocalMaxOn_sphere_of_isMax {g_r g_f : V} {ε : ℝ} {gt : V}
    (hgt_mem : gt ∈ feasibleSet g_r g_f)
    (hgt_max : ∀ y ∈ feasibleSet g_r g_f, ‖y‖ ≤ ε →
      nashObjective g_r g_f y ≤ nashObjective g_r g_f gt) :
    IsLocalMaxOn (nashObjective g_r g_f) {x : V | ‖x‖ = ε} gt := by
  have hmaxOn : IsMaxOn (nashObjective g_r g_f)
      ({x : V | ‖x‖ = ε} ∩ feasibleSet g_r g_f) gt := by
    intro y hy
    exact hgt_max y hy.2 (le_of_eq hy.1)
  have hlocal : IsLocalMaxOn (nashObjective g_r g_f)
      ({x : V | ‖x‖ = ε} ∩ feasibleSet g_r g_f) gt := hmaxOn.localize
  have hfeas_nhds : feasibleSet g_r g_f ∈ 𝓝 gt :=
    (isOpen_feasibleSet g_r g_f).mem_nhds hgt_mem
  have heq : 𝓝[{x : V | ‖x‖ = ε}] gt = 𝓝[{x : V | ‖x‖ = ε} ∩ feasibleSet g_r g_f] gt :=
    nhdsWithin_restrict' _ hfeas_nhds
  change IsMaxFilter (nashObjective g_r g_f) (𝓝[{x : V | ‖x‖ = ε}] gt) gt
  rw [heq]
  exact hlocal

end Munba
