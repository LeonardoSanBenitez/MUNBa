import MunbaProofs.ParetoImprovement
import MunbaProofs.LinearDependence
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Theorem 2.10 (Convergence)

`catalog.json`'s `theorem_2_10_convergence`. Paper statement: since each player's loss is
monotonically decreasing (Theorem 2.9) and bounded below, the combined loss converges, and the
limit point is a (Pareto) stationary point.

## Both halves are now formalized, with an explicit hypothesis for the one step the paper itself
## never rigorously derives

Theorem 2.10 has two parts of very different character:

1. The combined loss `L(θ^(t)) := L_r(θ^(t)) + L_f(θ^(t))` is monotonically non-increasing (from
   Theorem 2.9, applied at every step) and bounded below (each loss `≥ 0`), hence converges to a
   limit — a standard real-analysis fact (`tendsto_atTop_ciInf`, a monotone/antitone bounded
   sequence of reals converges to its infimum). Proved UNCONDITIONALLY:
   `theorem_2_10_combined_loss_converges`.
2. The paper further argues `η^(t)g̃^(t) → 0` as `t → ∞`, hence the combined gradient vanishes at
   the limit point `θ*`, giving stationarity, and (via `MunbaProofs.LinearDependence`) Pareto
   stationarity. `catalog.json`'s own `known_issues_in_paper` calls this "the least rigorous step
   in the paper's entire proof section" — the paper ASSERTS it without deriving it. A 2026-07-17
   investigation (see `catalog.json` and `PLAN-LEAN-PROOFS.md` for the full derivation) confirmed
   this step genuinely does NOT follow from anything proved elsewhere in the paper without an
   additional structural assumption the paper itself never states — backed by both an explicit
   counterexample to the paper's own Eq. (43) substitution, and an abandoned alternative proof
   found commented out in the authors' own LaTeX source that independently hits the same wall.

   **Explicit decision (2026-07-17, user instruction): formalize the paper's own full claim,
   taking the one step it does not derive as an explicit Lean hypothesis** — the same way
   `Optimality.lean` already takes existence of the constrained maximizer as an explicit
   hypothesis rather than deriving it, matching the paper's own scope. This is NOT an invitation
   to invent a different, stronger unpublished result, and NOT a mandate to instead chase the
   authors' own abandoned compactness-based alternative proof to reach a *weaker* conclusion —
   neither is the job here. See `theorem_2_10_stationarity`'s docstring below for exactly which
   hypothesis is added and why it is the most direct Lean reading of what the paper itself asserts
   at that step.
-/

namespace Munba

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] in
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

omit [CompleteSpace V] in
/-- Part 2 of Theorem 2.10 (Stationarity): if, at some point `θStar`, some POSITIVE combination of
the two players' gradients vanishes, the two gradients are linearly dependent — `θStar` is a
Pareto stationary point. This is exactly the paper's own literal closing argument ("at `θ*`,
`g̃ = α_r∇𝓛_r(θ*) + α_f∇𝓛_f(θ*) = 0` ... implies that the per-task gradients are linearly
dependent"), so it reuses `LinearDependence.lean`'s `gr_linearlyDependent_of_combination_eq_zero`
directly — no new mathematical content beyond what that file already proves.

## Why `hvanish` is an explicit HYPOTHESIS here, not a derived conclusion

The paper's own proof reaches `g̃(θ*) = 0` from `η^(t)g̃^(t) → 0` (`sec/X_suppl.tex` line 375 of
the `2411.15537v4` e-print) without a rigorous derivation, and — per the 2026-07-17 investigation
recorded in `catalog.json` — that step does not actually follow from the loss-convergence fact
this file DOES prove (`theorem_2_10_combined_loss_converges`), without a further structural
assumption the paper never states. There is therefore nothing legitimate to re-derive `hvanish`
FROM using only what is already proved here. Taking it as an explicit hypothesis, exactly where
the paper's own proof takes it as given, is the honest way to formalize the published statement
itself — bringing in what the paper claims, not more (a stronger result via a different invented
assumption) and not less (a weaker result via the authors' own abandoned alternative argument). -/
theorem theorem_2_10_stationarity {g_r_star g_f_star : V} {α_r α_f : ℝ}
    (hα_r_pos : 0 < α_r) (_hα_f_pos : 0 < α_f)
    (hvanish : α_r • g_r_star + α_f • g_f_star = 0) :
    g_r_star = (-α_f / α_r) • g_f_star :=
  gr_linearlyDependent_of_combination_eq_zero hα_r_pos.ne' hvanish

/-- Theorem 2.10 (Convergence), the paper's FULL statement, assembled from both halves: the
combined loss converges (unconditionally), AND, at the trajectory's limit point `θStar`, the two
players' gradients — `g_r_star`, `g_f_star`, tied to `𝓛_r`, `𝓛_f` via `HasGradientAt` so this is
genuinely about the actual gradients of the given loss functions, not arbitrary vectors — are
linearly dependent, i.e. `θStar` is Pareto stationary.

Two hypotheses here are NOT derived from anything else proved in this file, both because the
paper itself does not derive them either: `htheta_lim` (the paper writes "θ*" as if its existence
as an actual limit of the trajectory `θ` were already established, but loss-VALUE convergence,
which is proved, does not by itself imply the parameter SEQUENCE converges), and `hvanish` (see
`theorem_2_10_stationarity`'s docstring immediately above for the full justification). -/
theorem theorem_2_10_convergence (𝓛_r 𝓛_f : V → ℝ) (θ : ℕ → V) (θStar : V)
    (hLr_bdd : ∀ n, 0 ≤ 𝓛_r (θ n)) (hLf_bdd : ∀ n, 0 ≤ 𝓛_f (θ n))
    (hmono_r : ∀ n, 𝓛_r (θ (n + 1)) ≤ 𝓛_r (θ n))
    (hmono_f : ∀ n, 𝓛_f (θ (n + 1)) ≤ 𝓛_f (θ n))
    (_htheta_lim : Filter.Tendsto θ Filter.atTop (nhds θStar))
    {g_r_star g_f_star : V}
    (_hgrad_r : HasGradientAt 𝓛_r g_r_star θStar) (_hgrad_f : HasGradientAt 𝓛_f g_f_star θStar)
    {α_r α_f : ℝ} (hα_r_pos : 0 < α_r) (hα_f_pos : 0 < α_f)
    (hvanish : α_r • g_r_star + α_f • g_f_star = 0) :
    (∃ L : ℝ, Filter.Tendsto (fun n => 𝓛_r (θ n) + 𝓛_f (θ n)) Filter.atTop (nhds L)) ∧
      g_r_star = (-α_f / α_r) • g_f_star :=
  ⟨theorem_2_10_combined_loss_converges 𝓛_r 𝓛_f θ hLr_bdd hLf_bdd hmono_r hmono_f,
    theorem_2_10_stationarity hα_r_pos hα_f_pos hvanish⟩

end Munba
