import MunbaProofs.ParetoImprovement
import MunbaProofs.LinearDependence
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Theorem 2.10 (Convergence) — the combined-loss-converges part

`catalog.json`'s `theorem_2_10_convergence`. Paper statement: since each player's loss is
monotonically decreasing (Theorem 2.9) and bounded below, the combined loss converges, and the
limit point is a (Pareto) stationary point.

## Scope: this file proves the FIRST half only — read this before citing Theorem 2.10 as "done"

Theorem 2.10 has two parts of very different character:

1. The combined loss `L(θ^(t)) := L_r(θ^(t)) + L_f(θ^(t))` is monotonically non-increasing (from
   Theorem 2.9, applied at every step) and bounded below (each loss `≥ 0`), hence converges to a
   limit — a standard real-analysis fact (`tendsto_atTop_ciInf`, a monotone/antitone bounded
   sequence of reals converges to its infimum). Proved in full here.
2. The paper further argues `η^(t)g̃^(t) → 0` as `t → ∞`, hence the combined gradient vanishes at
   the limit point `θ*`, giving stationarity, and (via `MunbaProofs.LinearDependence`) Pareto
   stationarity. `catalog.json`'s own `known_issues_in_paper` calls this "the least rigorous step
   in the paper's entire proof section" — the paper ASSERTS it without deriving it; monotone
   convergence of the LOSS alone does not, by itself, imply the step-size-times-gradient product
   vanishes, without an additional summability argument (e.g. `Σ η^(t)‖g̃^(t)‖² < ∞`) or an
   explicit non-vanishing-step-size assumption, neither of which the paper states precisely
   enough to formalize as given. **NOT attempted here, deliberately, not silently.**
-/

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
/-- Part 1 of Theorem 2.10: if each player's loss along the MUNBa iteration is non-increasing
(Theorem 2.9's conclusion, applied at every step) and bounded below, the COMBINED loss
`𝓛_r(θ(n)) + 𝓛_f(θ(n))` converges as `n → ∞`. -/
theorem theorem_2_10_combined_loss_converges (𝓛_r 𝓛_f : V → ℝ) (θ : ℕ → V)
    (hLr_bdd : ∀ n, 0 ≤ 𝓛_r (θ n)) (hLf_bdd : ∀ n, 0 ≤ 𝓛_f (θ n))
    (hmono_r : ∀ n, 𝓛_r (θ (n + 1)) ≤ 𝓛_r (θ n))
    (hmono_f : ∀ n, 𝓛_f (θ (n + 1)) ≤ 𝓛_f (θ n)) :
    ∃ L : ℝ, Filter.Tendsto (fun n => 𝓛_r (θ n) + 𝓛_f (θ n)) Filter.atTop (nhds L) := by
  have hanti : Antitone (fun n => 𝓛_r (θ n) + 𝓛_f (θ n)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hr := hmono_r n
    have hf := hmono_f n
    linarith
  have hbdd : BddBelow (Set.range (fun n => 𝓛_r (θ n) + 𝓛_f (θ n))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    have hr := hLr_bdd n
    have hf := hLf_bdd n
    linarith
  exact ⟨_, tendsto_atTop_ciInf hanti hbdd⟩

end Munba
