module
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierCoverage
public import DecoupledConsensusProofs.Execution.SeedActionRowCarriage

/-!
# Carriage under a bounded action window

The existing honest triple covers the actual round rows when their delivery
deadlines precede its +2 proposal. The point schedule and three-slot rounds
discharge that bound without any additional proposer or delivery assumption.
The point instance also retains the original own-payload conclusion.
See PROTOCOL.md `sec:healing-schedule` and `proposal_attestations`.
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Execution Internal
open Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A delivery bound at +2 supplies the actual row to the selection pool;
GST is bounded by the existing paper-action premise. -/
theorem windowActionRow_mem_selectedRows_at_plusTwo_of_carrier_bound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    (hbound : ∀ v, (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2))
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.hc.opening_slot q + 2)).st := by
  have hpaper := action_add_delta_le_plusTwo_proposal_time S q
  have haHor : S.a q ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hpaper.trans hhor)
  have hslots : S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
    simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
      Nat.add_le_add_left S.hc.R_ge_two (q * S.hc.R)
  have hp := windowActionRow_mem_processedRows_of_deadline S adm hv
    (adm.all_awake v hv q hpost haHor) hcar.2.2 hhor
    (cut := Protocol.proposal_time S.E (S.hc.opening_slot q + 2))
    (by
      rw [← max_add_add_right]
      exact max_le (hbound v) ((Int.add_le_add_right hpost _).trans hpaper))
    (Protocol.proposal_time_mono S.E hslots) le_rfl
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  refine ⟨hp, ?_⟩
  have hr : (NamedActionReads.windowActionAttestationAt S rho v q).round = q := by
    change S.hc.round_of (NamedActionReads.windowActionReadAt S rho v q).st.core.s = q
    exact WindowAction.actionRead_round S v _ q
  rw [hr]
  exact inWindow_round_at_plusTwo S rho q

/-- Bounded actual actions give chain-or-own coverage at the existing triple's
last proposal (PROTOCOL.md `proposal_attestations`). -/
theorem plusTwoProposal_covers_roundRow_of_carrier_bound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    (hbound : ∀ v, (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2))
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations := by
  apply proposal_covers_resolvedRoundRow S adm _ hB
  · change (S.node v).val_index ∈ rho.honest
    simpa only [S.node_val_index] using hv
  · exact windowActionRow_mem_selectedRows_at_plusTwo_of_carrier_bound
      S adm hcar hpost hhor hbound hv

/-- The point schedule satisfies the carrier delivery bound at every round. -/
theorem carrier_bound_point (S : Setup V)
    (hpoint : ∀ v r, (S.node v).act r = S.a r) (q : Round) :
    ∀ v, (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  intro v
  rw [hpoint]
  exact action_add_delta_le_plusTwo_proposal_time S q

/-- For three-slot rounds P2 implies the carrier delivery bound. -/
theorem carrier_bound_of_R_eq_three (S : Setup V) (hR : S.hc.R = 3) (q : Round) :
    ∀ v, (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  intro v
  apply (S.act_pre_cutoff v q).trans
  rw [← S.deadlineProposalSlot_eq_plusTwo_of_R_eq_three hR q]
  exact (S.deadlineProposalSlot_le_iff q _).mp le_rfl

/-- The bounded-window instance of the internal coverage interface. -/
theorem carrierCoverage_of_carrier_bound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    (hbound : ∀ v, (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2)) :
    CarrierCoverage S rho q := by
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q + 2)
  intro v hv
  exact ⟨_, B, hcar.2.2, inWindow_round_at_plusTwo S rho q, hhor, hB,
    plusTwoProposal_covers_roundRow_of_carrier_bound S adm hcar hpost hhor hbound hB hv⟩

/-- The original point instance of carrier coverage, at the same +2 slot. -/
theorem carrierCoverage_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon) :
    CarrierCoverage S rho q :=
  carrierCoverage_of_carrier_bound S adm hcar hpost hhor (carrier_bound_point S hpoint q)

/-- At R = 3, the deadline-coverage producer supplies the interface directly. -/
theorem carrierCoverage_of_R_eq_three
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (hR : S.hc.R = 3)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon) :
    CarrierCoverage S rho q := by
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q + 2)
  intro v hv
  exact ⟨_, B, hcar.2.2, inWindow_round_at_plusTwo S rho q, hhor, hB,
    plusTwoProposal_covers_roundRow_of_R_eq_three S adm hR hcar hpost hhor hB hv⟩

/-- Point recovery retains own-payload carriage of the actual observer, not
just the weaker existential coverage interface. -/
theorem carrierCoverage_point_own_rows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B) :
    ∀ v ∈ rho.honest, NamedActionReads.windowActionAttestationAt S rho v q ∈
      B.attestations := by
  intro v hv
  rw [WindowAction.windowActionAttestationAt_point S rho v q (hpoint v q)]
  exact plusTwoProposal_carries_roundRow_point S adm hpoint hcar hpost hhor hB hv

#print axioms windowActionRow_mem_selectedRows_at_plusTwo_of_carrier_bound
#print axioms plusTwoProposal_covers_roundRow_of_carrier_bound
#print axioms carrier_bound_point
#print axioms carrier_bound_of_R_eq_three
#print axioms carrierCoverage_of_carrier_bound
#print axioms carrierCoverage_point
#print axioms carrierCoverage_of_R_eq_three
#print axioms carrierCoverage_point_own_rows

end DecoupledConsensusModel.Proofs.HealingSurface

end
