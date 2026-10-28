module
public import DecoupledConsensusModel

/-!
# Inputs at per-validator action times

Replays the clock, proposal, Goldfish vote, and confirmation stages that precede
an attestation in the shared scheduler (PROTOCOL.md `sec:public-handlers`).
Read the scheduler before this module and the window-action proofs after it.
-/
@[expose] public section

namespace DecoupledConsensusModel.Execution.NamedActionReads
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual input to attestation after every earlier duty at time `t`. -/
def windowReadFrom (S : Setup V) (v : V) (before : NamedNodeState V) (t : Time) :
    NamedNodeState V :=
  let cache := preparedCache S before t
  let gc := NamedProfile.gradeContract cache
  let s := S.E.slotOf t
  let st0 := NamedStore.setClock S.E before.st t
  let st1 := if 0 < s ∧ t = proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index then
    (NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = vote_time S.E s then
    (NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = support_cutoff S.E s then
    NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  ⟨st3, before.record, cache⟩

/-- The attestation input at the validator's own round action. -/
def windowActionReadFrom (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    NamedNodeState V := windowReadFrom S v before ((S.node v).act r)

/-- The strict-time run read followed by the actual action's preceding duties. -/
def windowActionReadAt (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedNodeState V :=
  windowActionReadFrom S v (NamedRun.stateBeforeTime S rho ((S.node v).act r) v) r

/-- The original row selected at the validator's own action time. -/
def windowActionAttestationAt (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedAttestation V :=
  let n := windowActionReadAt S rho v r
  (NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st n.record).2.2

end DecoupledConsensusModel.Execution.NamedActionReads
