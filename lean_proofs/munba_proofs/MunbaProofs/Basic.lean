import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Shared setup for the MUNBa formalization

Background notation shared by several catalog items (`catalog.json`'s `lemma_2_1_feasibility`,
`lemma_2_2_cone_property`).

## Ambient space

The paper writes `g_r, g_f ∈ ℝ^n` here (Lemma 2.1/2.2) but `θ ∈ ℝ^d` everywhere else, with `n`
and `d` never explicitly related (`catalog.json`'s `known_issues_in_paper` for Lemma 2.1). We
sidestep this by working in an arbitrary real inner product space `V`, which specializes to either
reading (`ℝ^n`, `EuclideanSpace ℝ (Fin d)`, ...) at no cost and avoids committing to one.

## The `u_r`, `u_f` type-signature issue

`catalog.json` flags that the paper's own stated type `u_r, u_f : ℝ^n × ℝ^n → ℝ` (binary) does not
match how they are actually used in Eqs. (2)-(3): the player's gradient (`g_r` or `g_f`) is fixed
data, and the only real argument is the candidate joint direction `g̃`. `utility` below resolves
this by making the gradient an explicit first argument and the candidate direction the argument
the function is "really" about — i.e. `utility g` is the intended unary functional for a fixed
gradient `g`.
-/

open scoped RealInnerProductSpace

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The utility of a candidate joint update direction `gt` ("g-tilde") for a player with gradient
`g`, i.e. `u_r`/`u_f` from Eqs. (2)-(3) of the paper, curried at the fixed gradient. -/
def utility (g gt : V) : ℝ := ⟪g, gt⟫

/-- The feasible set `C` of Lemma 2.1: joint directions that are simultaneously an improvement for
both a player with gradient `g1` and a player with gradient `g2`. -/
def feasibleSet (g1 g2 : V) : Set V := {gt | 0 < utility g1 gt ∧ 0 < utility g2 gt}

@[simp]
theorem mem_feasibleSet {g1 g2 gt : V} :
    gt ∈ feasibleSet g1 g2 ↔ 0 < utility g1 gt ∧ 0 < utility g2 gt := Iff.rfl

end Munba
