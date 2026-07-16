import MunbaProofs.Basic
import MunbaProofs.ConeProperty
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Building block for Theorem 2.3: the Nash-bargaining objective and its scale-shift identity

`catalog.json`'s `theorem_2_3_optimality_condition`. This file is the first of several building
blocks toward Theorem 2.3 (mirrors how the I-CARE project built `ResidualGraph.lean`/
`AugmentingPath.lean` before assembling `MaxFlowMinCut.lean` — a genuinely hard paper result gets
its own supporting infrastructure, not one monolithic proof).

Defines MUNBa's objective `f(g̃) = log(u_r(g̃)) + log(u_f(g̃))` (the paper's Eq. 4/15, in log
form) and proves a fact the paper's own proof of Theorem 2.3 never states explicitly, but needs:
**the paper never argues why the ball constraint `‖g̃‖ ≤ ε` is active at the optimum** (flagged in
`catalog.json`'s `known_issues_in_paper`: "the proof never argues λ != 0 ... i.e. that the
norm-ball constraint is ACTUALLY active/binding"). We supply that argument here, purely
algebraically (no differential calculus needed for this half): since `u_r, u_f` are linear, `f`
has a clean scale-shift identity under positive rescaling, which combined with Lemma 2.2 (`C` is a
cone) forces any maximizer to sit exactly on the boundary of the ball.
-/

namespace Munba

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- MUNBa's Nash-bargaining log-objective, `f(g̃) := log(u_r(g̃)) + log(u_f(g̃))`, the paper's
Eq. (4) rewritten in log form (used throughout Sec. 6's proof of Theorem 2.3, e.g. Eq. 15). Total
on all of `V` for convenience (via `Real.log`'s junk value `log x = 0` for `x ≤ 0`); only
meaningful as MUNBa's actual objective at points of `feasibleSet g_r g_f`. -/
noncomputable def nashObjective (g_r g_f gt : V) : ℝ :=
  Real.log (utility g_r gt) + Real.log (utility g_f gt)

/-- The scale-shift identity: rescaling a feasible direction by a positive scalar `t` shifts the
objective additively by `2 log t`, independent of the direction itself. This is what makes the
ball constraint's boundary strictly better than its interior (Step towards Theorem 2.3). Not
stated in the paper (which does not address why the ball constraint binds at all), but immediate
from `u_r, u_f` being linear (`utility_pos_homogeneous`, `ConeProperty.lean`) and `Real.log`'s
multiplicative-to-additive property. -/
theorem nashObjective_smul (g_r g_f gt : V) {t : ℝ} (ht : 0 < t)
    (hgt : gt ∈ feasibleSet g_r g_f) :
    nashObjective g_r g_f (t • gt) = nashObjective g_r g_f gt + 2 * Real.log t := by
  obtain ⟨hr, hf⟩ := hgt
  have hr' : utility g_r (t • gt) = t * utility g_r gt := utility_pos_homogeneous g_r t ht gt
  have hf' : utility g_f (t • gt) = t * utility g_f gt := utility_pos_homogeneous g_f t ht gt
  unfold nashObjective
  rw [hr', hf', Real.log_mul (ne_of_gt ht) (ne_of_gt hr), Real.log_mul (ne_of_gt ht) (ne_of_gt hf)]
  ring

/-- A feasible direction is never `0` — `u_r(0) = 0` is not `> 0`. Small but used repeatedly:
lets us divide by `‖gt‖`. -/
theorem ne_zero_of_mem_feasibleSet {g_r g_f gt : V} (hgt : gt ∈ feasibleSet g_r g_f) : gt ≠ 0 := by
  rintro rfl
  have hr := hgt.1
  simp [utility] at hr

/-- **The ball constraint is active at any maximizer** (the step `catalog.json` flags the paper as
never arguing): if `gt` maximizes MUNBa's objective over `feasibleSet g_r g_f` intersected with
the closed ball of radius `ε`, then `‖gt‖ = ε` exactly — the maximizer cannot lie in the ball's
interior. Proof: if `‖gt‖ < ε`, scaling `gt` up to the boundary (`t := ε / ‖gt‖ > 1`) stays
feasible (Lemma 2.2, `C` is a cone) and stays in the ball (`‖t • gt‖ = ε`), while strictly
increasing the objective (`nashObjective_smul` + `Real.log` strictly increasing, `t > 1`) —
contradicting maximality. -/
theorem norm_eq_of_isMax {g_r g_f : V} {ε : ℝ} (hε : 0 < ε) {gt : V}
    (hgt_mem : gt ∈ feasibleSet g_r g_f) (hgt_ball : ‖gt‖ ≤ ε)
    (hgt_max : ∀ y ∈ feasibleSet g_r g_f, ‖y‖ ≤ ε →
      nashObjective g_r g_f y ≤ nashObjective g_r g_f gt) :
    ‖gt‖ = ε := by
  by_contra hne
  have hlt : ‖gt‖ < ε := lt_of_le_of_ne hgt_ball hne
  have hgt0 : gt ≠ 0 := ne_zero_of_mem_feasibleSet hgt_mem
  have hnormpos : (0:ℝ) < ‖gt‖ := norm_pos_iff.mpr hgt0
  set t : ℝ := ε / ‖gt‖ with ht_def
  have ht1 : 1 < t := by
    rw [ht_def, lt_div_iff₀ hnormpos]
    linarith
  have ht0 : 0 < t := lt_trans one_pos ht1
  have hmem' : t • gt ∈ feasibleSet g_r g_f := lemma_2_2_cone_property g_r g_f hgt_mem ht0
  have hnorm' : ‖t • gt‖ = ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht_def]
    field_simp
  have hball' : ‖t • gt‖ ≤ ε := le_of_eq hnorm'
  have hbetter := hgt_max (t • gt) hmem' hball'
  rw [nashObjective_smul g_r g_f gt ht0 hgt_mem] at hbetter
  have hlogpos : 0 < Real.log t := Real.log_pos ht1
  linarith

end Munba
