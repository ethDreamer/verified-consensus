module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol (derive_named)
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
















/-! ## Indexed action-read bridge -/

/-- The event input equals the strict-time window read at its actual tick
(PROTOCOL.md `sec:public-handlers`). -/
theorem actionEventRead_eq_windowActionReadAt_of_tick
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {r : Round}
    (hi : rho.events[i]? = some (Event.tick v ((S.node v).act r))) :
    actionEventRead S rho i v r = NamedActionReads.windowActionReadAt S rho v r := by
  change NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r =
    NamedActionReads.windowActionReadFrom S v
      (NamedRun.stateBeforeTime S rho ((S.node v).act r) v) r
  exact congrArg (fun before => NamedActionReads.windowActionReadFrom S v before r)
    (Proofs.NamedRuntime.tick_prefix_eq_strict S rho sch.sorted
      (NamedScheduleWellFormed.nodup sch) hi)

/-- A paper-time tick has the original action input when the validator's
actual action is at that instant (PROTOCOL.md `sec:healing-schedule`). -/
theorem actionEventRead_eq_actionReadAt_of_tick
    (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {r : Round}
    (hi : rho.events[i]? = some (Event.tick v (S.a r)))
    (hact : (S.node v).act r = S.a r) :
    actionEventRead S rho i v r = Proofs.HealingSurface.actionReadAt S rho v r := by
  unfold actionEventRead NamedActionReads.windowActionReadFrom
  rw [hact, Proofs.WindowAction.windowReadFrom_point]
  exact congrArg (fun before => NamedActionReads.actionReadFrom S before r)
    (Proofs.NamedActionSources.action_read_index S rho sch i v r hi)

/-- An actual emission at the paper tick supplies the local point equality
and identifies its round (PROTOCOL.md `sec:public-handlers`). -/
theorem actionEventRead_eq_actionReadAt_of_emission_at_paper_tick
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {r : Round} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (Event.tick v (S.a r)))
    (ha : Object.attest a ∈ NamedRun.emittedAt S rho i v (S.a r)) :
    a.round = r ∧ actionEventRead S rho i v r = Proofs.HealingSurface.actionReadAt S rho v r := by
  have ht := (Proofs.WindowAction.run_emission_fields S
    (show rho.emits S v (.attest a) (S.a r) from ⟨i, hi, ha⟩)).1
  have hr : a.round = r := by
    calc
      a.round = S.hc.round_of (S.E.slotOf (S.a r)) := by rw [ht, S.act_round]
      _ = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  rw [hr] at ht
  exact ⟨hr, actionEventRead_eq_actionReadAt_of_tick S sch hi ht.symm⟩















/-! ## Named prefix source projections -/





/-! ## Source history at a time cutoff -/















#print axioms honestAttestationOutputPreceqAtIndex_of_activeSources
#print axioms actionEventRead_eq_actionReadAt_of_emission_at_paper_tick
#print axioms actionEventRead_eq_windowActionReadAt_of_tick
#print axioms actionEventRead_eq_actionReadAt_of_tick

end Protocol
end DecoupledConsensusModel

end
