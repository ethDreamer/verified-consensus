module
public import DecoupledConsensusInternal.Definitions.NamedJointOutageEvents
public import DecoupledConsensusProofs.Execution.IdxGaps

/-!
# Strict causal history of accepted carriers

Unforgeability orders each original honest row before delivery; self-proposals
select rows from their strict prior state. Ancestral carriers are handled by
their own acceptance events, so their emission bounds are strict as well.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedCausalCarrierHistory
open Execution Protocol Internal.NamedJointOutage Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Both acceptance paths put a carried honest row's emission strictly
before the carrier acceptance, including equal-time self-proposals. -/
theorem row_emission_index_lt_block_acceptance
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (carrier : NamedBlock V) (j : Nat) (received : Time)
    (hacc : NamedRun.acceptsAt S rho j v (.block carrier) received)
    (a : NamedAttestation V) (hrow : a ∈ carrier.attestations) (ha : a.val_index ∈ rho.honest)
    (k : Nat) (sent : Time) (hk : rho.events[k]? = some (.tick a.val_index sent))
    (hemit : NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index sent)
    (hsend : sent ≤ received) : k < j := by
  obtain ⟨hcallIdx, e, he, _, het⟩ := hacc.1
  change NamedRun.processesAtIndex S rho j v (.block carrier) at hcallIdx
  rcases hcallIdx with ⟨time, hji, hemC⟩ | ⟨time, hji⟩
  · have heq : NamedEvent.tick v time = e := Option.some.inj (hji.symm.trans he)
    have htime : time = received := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst htime
    exact emission_index_lt_self_proposed_carrier S rho core j v time carrier
      hji hemC a hrow ha k sent hk hemit hsend
  · have heq : NamedEvent.deliver v (.block carrier) time = e :=
      Option.some.inj (hji.symm.trans he)
    have htime : time = received := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst htime
    exact tick_lt_of_deliver_index rho core.sorted hji hk hsend

/-- A held honest SG row was emitted inside the strict event prefix,
including self-admission at its own tick (PROTOCOL.md#on_attestation). -/
theorem held_row_emission_before (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (n : Nat) (v : V)
    {a : NamedAttestation V}
    (hrow : a ∈ (NamedRun.stateBefore S rho n v).st.sg_rows a.round)
    (ha : a.val_index ∈ rho.honest) :
    ∃ i, i < n ∧
      rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
        ((S.node a.val_index).act a.round) := by
  obtain ⟨j, hj, received, hacc, hsend, k, hk, hem⟩ :=
    NamedOutageProvenance.honest_held_row_emission S rho core.toNamedUnforgeable n v hrow ha
  obtain ⟨hcall, e, he, _, het⟩ := hacc.1
  rcases hcall with (⟨time, htick, hself⟩ | ⟨time, hdeliver⟩) |
    ⟨B, pos, before, hblock, _, _, hmember⟩
  · have hfields := WindowAction.run_emission_fields S ⟨j, htick, hself⟩
    have hsame : rho.events[j]? = some
        (.tick a.val_index ((S.node a.val_index).act a.round)) := by
      simpa only [hfields.2.2, hfields.1] using htick
    have hkj : k = j :=
      (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hk).1 core.nodup).mp
        (hk.trans hsame.symm)
    exact ⟨k, hkj ▸ hj, hk, hem⟩
  · have heq : NamedEvent.deliver v (.attest a) time = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htime : time = received := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst htime
    exact ⟨k, (tick_lt_of_deliver_index rho core.sorted hdeliver hk hsend).trans hj, hk, hem⟩

  · have hmem : a ∈ B.attestations := List.mem_of_getElem? hmember
    rcases hblock with ⟨time, hdeliver, _⟩ | ⟨time, htick, hblockemit, _⟩
    · have heq : NamedEvent.deliver v (.block B) time = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htime : time = received := by
        simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
      subst htime
      exact ⟨k, (tick_lt_of_deliver_index rho core.sorted hdeliver hk hsend).trans hj,
        hk, hem⟩
    · have heq : NamedEvent.tick v time = e := Option.some.inj (htick.symm.trans he)
      have htime : time = received := by
        simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
      subst htime
      exact ⟨k, (emission_index_lt_self_proposed_carrier S rho core j v time B
        htick hblockemit a hmem ha k _ hk hem hsend).trans hj, hk, hem⟩

/-- All ancestral honest rows in a body held after event `j` were emitted
strictly before `j`. This also covers bodies retained from earlier events. -/
theorem held_carrier_rows_before (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (j : Nat) (v : V) {B : NamedBlock V}
    (hB : B ∈ (NamedRun.stateBefore S rho (j + 1) v).st.bodies) :
    CausalCarrierRowsBefore S rho j B := by
  intro A hAB a hrow ha
  obtain ⟨k, hkj, received, hacc, hsend, i, hi, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      core.toNamedUnforgeable (j + 1) v hB hAB hrow ha
  have hik := row_emission_index_lt_block_acceptance S rho core v A k received hacc
    a hrow ha i _ hi hem hsend
  exact ⟨i, lt_of_lt_of_le hik (Nat.le_of_lt_succ hkj), hi, hem⟩

/-- The causal history needed at a carrier receipt is strictly earlier than
that receipt, rather than merely earlier than the next event prefix. -/
theorem accepted_carrier_rows_before (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (j : Nat) (v : V) (t : Time) {B : NamedBlock V}
    (hacc : NamedRun.acceptsAt S rho j v (.block B) t) :
    CausalCarrierRowsBefore S rho j B := by
  apply held_carrier_rows_before S rho core j v
  simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2

#print axioms held_row_emission_before
#print axioms row_emission_index_lt_block_acceptance
#print axioms held_carrier_rows_before
#print axioms accepted_carrier_rows_before

end DecoupledConsensusModel.Proofs.NamedCausalCarrierHistory
