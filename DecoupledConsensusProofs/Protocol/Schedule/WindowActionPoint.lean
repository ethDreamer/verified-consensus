module
public import DecoupledConsensusProofs.Protocol.Schedule.WindowAction
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedActionReads

/-!
# Scheduler reads at the paper instant

The paper instant is a support cutoff, so its prepared input includes only
confirmation. This read equation does not assert that an action occurs there
(PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.WindowAction
open Execution Protocol NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

/-- At the paper instant, only confirmation precedes a possible attestation. -/
theorem windowReadFrom_point (S : Setup V) (v : V) (before : NamedNodeState V)
    (r : Round) :
    windowReadFrom S v before (S.a r) = actionReadFrom S before r := by
  have hslot : 0 < S.E.slotOf (S.a r) := by
    rw [Setup.a, a_eq_support_cutoff_succ, Optimistic.slotOf_support_cutoff]
    exact Nat.zero_lt_succ _
  have hsupport : S.a r = support_cutoff S.E (S.E.slotOf (S.a r)) := by
    rw [Setup.a, a_eq_support_cutoff_succ, Optimistic.slotOf_support_cutoff]
  have hconfirm : 0 < S.E.slotOf (S.a r) ∧
      S.a r = support_cutoff S.E (S.E.slotOf (S.a r)) := ⟨hslot, hsupport⟩
  have hp := Optimistic.a_ne_proposal_time S (t := S.a r) (r := r) rfl
  have hv := Optimistic.a_ne_vote_time S (t := S.a r) (r := r) rfl
  have hproposal : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = proposal_time S.E (S.E.slotOf (S.a r)) ∧
      S.E.proposer (S.E.slotOf (S.a r)) = (S.node v).val_index) := fun h => hp h.2.1
  have hvote : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = vote_time S.E (S.E.slotOf (S.a r))) := fun h => hv h.2
  unfold windowReadFrom
  dsimp only
  rw [ite_eq_right hproposal, ite_eq_right hvote, ite_eq_left hconfirm]
  rfl

/-- The strict-time actual read recovers the paper observer at a locally
coincident action (PROTOCOL.md `sec:healing-schedule`). -/
theorem windowActionReadAt_point (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (hact : (S.node v).act r = S.a r) :
    windowActionReadAt S rho v r = actionReadAt S rho v r := by
  unfold windowActionReadAt windowActionReadFrom
  rw [hact, windowReadFrom_point]
  rfl

/-- Exact attestation observers coincide at a locally point-scheduled action
(PROTOCOL.md `sec:healing-schedule`). -/
theorem windowActionAttestationAt_point (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (hact : (S.node v).act r = S.a r) :
    windowActionAttestationAt S rho v r = Proofs.HealingSurface.actionAttestationAt S rho v r := by
  unfold windowActionAttestationAt
  rw [windowActionReadAt_point S rho v r hact]
  rfl

#print axioms windowActionReadAt_point
#print axioms windowActionAttestationAt_point

end DecoupledConsensusModel.Proofs.WindowAction
