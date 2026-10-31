module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint
public import DecoupledConsensusProofs.Protocol.Schedule.DeadlineProposal

/-!
# Honest round rows at proposal deadlines

P2 bounds every action's delivery deadline by the next early G2 cutoff.
The existing GST premise also bounds outage-delayed arrivals by this cutoff.
Actual receipt inputs retain the exact named row; the proposal pool selects
it while its round remains eligible. On-chain exclusion then gives parent-chain
or own-payload coverage (PROTOCOL.md `sec:grades`, `proposal_attestations`).

The first public proposal after the cutoff is still in the row's round.
Its honesty is a separate consumer obligation. At the point schedule the
earlier action-plus-delay cutoff recovers the original +2 producer and its
own-payload specialization.
-/
@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Admission window at the point instance -/

omit [DecidableEq V] [Fintype V] in
/-- The `+2` slot names the round itself or its successor: `R ≥ 2` keeps it
inside the two opening slots that bracket it. -/
private theorem round_of_opening_add_two_bounds
    (hc : Protocol.HealConfig) (q : Round) :
    q ≤ hc.round_of (hc.opening_slot q + 2) ∧
      hc.round_of (hc.opening_slot q + 2) ≤ q + 1 := by
  have hR0 : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  have hopen : hc.opening_slot q = q * hc.R := rfl
  constructor
  · show q ≤ (hc.opening_slot q + 2) / hc.R
    rw [hopen]
    calc q = q * hc.R / hc.R := (Nat.mul_div_cancel q hR0).symm
      _ ≤ (q * hc.R + 2) / hc.R := Nat.div_le_div_right (Nat.le_add_right _ _)
  · show (hc.opening_slot q + 2) / hc.R ≤ q + 1
    rw [hopen]
    have hle : q * hc.R + 2 ≤ (q + 1) * hc.R := by
      have := hc.R_ge_two
      calc q * hc.R + 2 ≤ q * hc.R + hc.R := Nat.add_le_add_left this _
        _ = (q + 1) * hc.R := by ring
    calc (q * hc.R + 2) / hc.R ≤ (q + 1) * hc.R / hc.R :=
          Nat.div_le_div_right hle
      _ = q + 1 := Nat.mul_div_cancel _ hR0

/-- `omega` unfolds `HealConfig.round_of` into a division by the variable `R`,
so the one arithmetic step is stated on opaque naturals. -/
private theorem nat_sub_le_of_le_succ {x e q : Nat}
    (hx : x ≤ q + 1) (he : 1 ≤ e) : x - e ≤ q := by omega

/-- The prepared `+2` proposer read carries the `+2` slot's own clock. -/
private theorem proposerReadAt_slot (S : Setup V) (rho : Run V) (s : Slot) :
    (proposerReadAt S rho s).st.core.s = s := by
  simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using Proofs.Optimistic.slotOf_proposal_time S.E s

/-- **Round `q` is inside the `+2` proposer's SG admission window.** The `+2`
slot names round `q` or `q + 1`; the second case is covered by `η_SG ≥ 1`. -/
theorem inWindow_round_at_plusTwo (S : Setup V) (rho : Run V) (q : Round) :
    Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho (S.hc.opening_slot q + 2)).st.core q = true := by
  obtain ⟨hlo, hhi⟩ := round_of_opening_add_two_bounds S.hc q
  have hslot : (proposerReadAt S rho (S.hc.opening_slot q + 2)).st.core.s =
      S.hc.opening_slot q + 2 :=
    proposerReadAt_slot S rho (S.hc.opening_slot q + 2)
  have hone : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  unfold Protocol.ProposalRows.inWindow
  rw [hslot, decide_eq_true_eq]
  exact ⟨nat_sub_le_of_le_succ hhi hone, hlo⟩

/-! ## Exact named rows at a proposal input -/

/-- An honest emitter's exact named row is in the prepared proposal read's own
processed rows once its erasure is in the duty store's processed pool. -/
private theorem exactActionRow_mem_namedProcessed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {a : NamedAttestation V} {sent : Time}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) sent)
    (hprocessed : a.erase ∈
      (Protocol.proposerDutyStore S rho s).processed_attestations S.hc) :
    a ∈ Protocol.NamedProposalRows.processedRows S.hc
      (proposerReadAt S rho s).st := by
  let st := (proposerReadAt S rho s).st
  have hPool : NamedStore.PoolView st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using!
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.proposal_time S.E s)
          (S.E.proposer s)).1.1.1.2.2.2.1
  have hmap := NamedProposalRows.processed_rows_erasure S.hc st hPool
  have hmemMap : a.erase ∈
      (Protocol.NamedProposalRows.processedRows S.hc st).map
        NamedAttestation.erase := by
    rw [hmap]
    simpa only [st, Protocol.proposerDutyStore, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using!
        hprocessed
  obtain ⟨b, hb, hberase⟩ := List.mem_map.mp hmemMap
  have hbFlat := hb
  rw [Protocol.NamedProposalRows.processedRows] at hbFlat
  obtain ⟨k, -, hbk⟩ := List.mem_flatMap.mp hbFlat
  have hrounds : Proofs.NamedStoreBridge.SgRowRounds st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using!
        Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime S rho
          (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hbr : b.round = k := hrounds k b hbk
  have hbOwn : b ∈ st.sg_rows b.round := by
    rw [hbr]
    exact hbk
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E s)
  have hbN : b ∈
      (rho.stateBefore S n (S.E.proposer s)).st.sg_rows b.round := by
    rw [← congrFun hn (S.E.proposer s)]
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using! hbOwn
  have hbval : b.val_index = a.val_index :=
    congrArg CombinedAttestation.val_index hberase
  have hbHon : b.val_index ∈ rho.honest := by
    rw [hbval]
    exact haHon
  obtain ⟨_, _, _, _, _, hbEmit⟩ :=
    Proofs.Bridges.heldArePastEmissions_of_admissibleCore
      S adm.toNamedAdmissibleCore n (S.E.proposer s) hbN hbHon
  have hbEmit' : rho.emits S a.val_index
      (Object.attest b) ((S.node a.val_index).act b.round) := by
    simpa only [hbval] using hbEmit
  have hround : b.round = a.round :=
    congrArg CombinedAttestation.round hberase
  have hba : b = a := Proofs.Optimistic.emits_attest_unique S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    hbEmit' hemit hround
  simpa only [st, hba] using hb

/-- Actual rows reach a proposal input after a bounded delivery deadline.
The receipt remains in the action's round; the proposal itself may be later
(PROTOCOL.md `sec:public-handlers`). -/
theorem windowActionRow_mem_processedRows_of_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hawake : (S.node v).awake q = true)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {cut : Time}
    (hdeadline : max ((S.node v).act q) S.E.t_GST + S.E.Δ ≤ cut)
    (hround : cut ≤ Protocol.opening S.E S.hc (q + 1))
    (hcut : cut ≤ Protocol.proposal_time S.E s) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.processedRows S.hc (proposerReadAt S rho s).st := by
  let a := NamedActionReads.windowActionAttestationAt S rho v q
  have hmax : (S.node v).act q + S.E.Δ ≤
      max ((S.node v).act q) S.E.t_GST + S.E.Δ := by
    gcongr
    exact le_max_left _ _
  have hact : (S.node v).act q < cut :=
    (lt_add_of_pos_right _ S.E.Δ_pos).trans_le (hmax.trans hdeadline)
  have hem := WindowAction.honest_emits_action S adm.toNamedScheduleWellFormed hv q
    hawake (hact.le.trans (hcut.trans hhor))
  have hf := WindowAction.run_emission_fields S hem
  have hval : a.val_index = v := hf.2.2
  have hr : a.round = q := by
    have hh := S.act_round v a.round
    rw [← hf.1] at hh
    exact hh.symm.trans (S.act_round v q)
  have ha : a.val_index ∈ rho.honest := hval ▸ hv
  have hem' : NamedRun.emits S rho a.val_index (.attest a) ((S.node v).act q) := by
    rw [hval]
    exact hem
  obtain ⟨td, hlo, hhi, i, hcall⟩ := adm.broadcast v hv (.attest a)
    ((S.node v).act q) hem (S.E.proposer s) hprop
    (hdeadline.trans (hcut.trans hhor)) rfl
  have hrow := NamedSGArrival.honest_row_after_call_before_next_opening S rho
    adm.toNamedScheduleWellFormed adm.toNamedUnforgeable ha hem' hcall hlo
    (by rw [hr]; exact hhi.trans_le (hdeadline.trans hround))
  have hpool := NamedAdmission.pool_view_mem _
    (NamedRuntime.stateBefore_invariants S rho (i + 1) (S.E.proposer s)).1.1.1.2.2.2.1
    a hrow
  obtain ⟨_, e, he, _, htime⟩ := hcall
  have hretained := Protocol.attest_mem_stateBeforeTime_of_post S
    adm.toNamedScheduleWellFormed he
    (show e.time < Protocol.proposal_time S.E s from
      htime ▸ hhi.trans_le (hdeadline.trans hcut)) hpool
  have hduty : a.erase ∈ (Protocol.proposerDutyStore S rho s).sg_pool a.round := by
    simpa only [Protocol.proposerDutyStore, Optimistic.tickStore, Run.storeBeforeTime]
      using! hretained
  have hslots : S.hc.opening_slot q ≤ s := by
    by_contra hn
    have hm := Protocol.proposal_time_mono_local S.E
      (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    exact (not_le_of_gt ((S.opening_le_act v q).trans_lt (hact.trans_le hcut))) hm
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_three; omega
  have hrs : q ≤ S.hc.round_of s := by
    have hh : S.hc.opening_slot q / S.hc.R ≤ s / S.hc.R :=
      Nat.div_le_div_right hslots
    simpa only [Protocol.HealConfig.opening_slot, Nat.mul_div_cancel _ hR,
      Protocol.HealConfig.round_of] using hh
  apply exactActionRow_mem_namedProcessed S adm ha hem'
  apply Protocol.mem_processed_attestations_of_pool S.hc _ hduty
  simpa only [Protocol.proposerDutyStore, Optimistic.tickStore,
    Optimistic.slotOf_proposal_time, NamedAttestation.erase, hr] using hrs

/-- P2 and the existing GST bound place the whole delivery interval before
next-round early G2, including actions sent before GST (PROTOCOL.md `sec:grades`). -/
theorem windowActionRow_mem_processedRows_at_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {s : Slot} (hpost : S.E.t_GST ≤ S.a q)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hcut : Protocol.early S.E S.hc (q + 1) .g2 ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.processedRows S.hc (proposerReadAt S rho s).st := by
  have hpaper := S.hc.a_pre_cutoff S.E q
  have haHor : S.a q ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hpaper.trans (hcut.trans hhor))
  apply windowActionRow_mem_processedRows_of_deadline S adm hv
    (adm.all_awake v hv q hpost haHor) hprop hhor (cut := Protocol.early S.E S.hc (q + 1) .g2)
  · by_cases hg : S.E.t_GST ≤ (S.node v).act q
    · rw [max_eq_left hg]
      exact S.act_pre_cutoff v q
    · rw [max_eq_right (le_of_not_ge hg)]
      exact (Int.add_le_add_right hpost S.E.Δ).trans hpaper
  · have hd := S.E.Δ_pos
    simp only [Protocol.early, Protocol.Phase.earlyOffset]
    linarith
  · exact hcut

/-- Availability supplies selection whenever the round is still eligible in
this proposal's admission window (PROTOCOL.md `proposal_attestations`). -/
theorem windowActionRow_mem_selectedRows_at_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {s : Slot} (hpost : S.E.t_GST ≤ S.a q)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hcut : Protocol.early S.E S.hc (q + 1) .g2 ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hwindow : Protocol.ProposalRows.inWindow S.hc (proposerReadAt S rho s).st.core q = true)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc (proposerReadAt S rho s).st := by
  have hp := windowActionRow_mem_processedRows_at_deadline S adm hpost hprop hcut hhor hv
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  refine ⟨hp, ?_⟩
  have hr : (NamedActionReads.windowActionAttestationAt S rho v q).round = q := by
    change S.hc.round_of (NamedActionReads.windowActionReadAt S rho v q).st.core.s = q
    exact WindowAction.actionRead_round S v _ q
  simpa only [hr] using hwindow

/-- The point schedule recovers the original +2 selection contract from its
own earlier delivery deadline (PROTOCOL.md `sec:healing-schedule`). -/
theorem actionAttestationAt_mem_selectedRows_at_plusTwo_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    actionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.hc.opening_slot q + 2)).st := by
  have hdelay := action_add_delta_le_plusTwo_proposal_time S q
  have haHor : S.a q ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hdelay.trans hhor)
  have hp := windowActionRow_mem_processedRows_of_deadline S adm hv
    (adm.all_awake v hv q hpost haHor) hcar.2.2 hhor
    (cut := S.a q + S.E.Δ)
    (by rw [hpoint, max_eq_left hpost])
    (by
      have hh := S.hc.a_pre_cutoff S.E q
      have hd := S.E.Δ_pos
      simp only [Protocol.early, Protocol.Phase.earlyOffset] at hh
      exact hh.trans (by linarith)) hdelay
  rw [WindowAction.windowActionAttestationAt_point S rho v q (hpoint v q)] at hp
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  refine ⟨hp, ?_⟩
  rw [(actionAttestationAt_shape S rho v q).2.1]
  exact inWindow_round_at_plusTwo S rho q

/-- The first public proposal after the cutoff still admits this round's
rows (PROTOCOL.md `proposal_attestations`). -/
theorem inWindow_round_at_deadlineProposal (S : Setup V) (rho : Run V) (q : Round) :
    Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho (S.deadlineProposalSlot q)).st.core q = true := by
  unfold Protocol.ProposalRows.inWindow
  rw [proposerReadAt_slot, S.deadlineProposal_round, decide_eq_true_eq]
  exact ⟨Nat.sub_le _ _, le_rfl⟩

/-- Every honest round row is selected by an honest first-deadline proposer
(PROTOCOL.md `proposal_attestations`). -/
theorem windowActionRow_mem_selectedRows_at_first_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hprop : S.E.proposer (S.deadlineProposalSlot q) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (S.deadlineProposalSlot q) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.deadlineProposalSlot q)).st :=
  windowActionRow_mem_selectedRows_at_deadline S adm hpost hprop
    ((S.deadlineProposalSlot_le_iff q _).mp le_rfl) hhor
    (inWindow_round_at_deadlineProposal S rho q) hv

/-- After the deadline, every eligible honest round row is on the proposal's
parent chain or in its own payload (PROTOCOL.md `proposal_attestations`). -/
theorem proposal_covers_windowActionRow_at_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {s : Slot} (hpost : S.E.t_GST ≤ S.a q)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hcut : Protocol.early S.E S.hc (q + 1) .g2 ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hwindow : Protocol.ProposalRows.inWindow S.hc (proposerReadAt S rho s).st.core q = true)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations := by
  apply proposal_covers_resolvedRoundRow S adm s hB
  · change (S.node v).val_index ∈ rho.honest
    simpa only [S.node_val_index] using hv
  · exact windowActionRow_mem_selectedRows_at_deadline S adm hpost hprop hcut hhor hwindow hv

/-- An honest first-deadline proposal covers every honest round row
(PROTOCOL.md `proposal_attestations`). -/
theorem firstDeadlineProposal_covers_roundRow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hprop : S.E.proposer (S.deadlineProposalSlot q) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (S.deadlineProposalSlot q) ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.deadlineProposalSlot q) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations :=
  proposal_covers_windowActionRow_at_deadline S adm hpost hprop
    ((S.deadlineProposalSlot_le_iff q _).mp le_rfl) hhor
    (inWindow_round_at_deadlineProposal S rho q) hB hv

/-- For three-slot rounds, the existing carrier supplies the deadline
proposer's honesty, without any additional proposer premise
(PROTOCOL.md `sec:healing-schedule`). -/
theorem plusTwoProposal_covers_roundRow_of_R_eq_three
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hR : S.hc.R = 3) {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations := by
  have hs := S.deadlineProposalSlot_eq_plusTwo_of_R_eq_three hR q
  exact firstDeadlineProposal_covers_roundRow S adm hpost
    (by simpa only [hs] using hcar.2.2)
    (by simpa only [hs] using hhor)
    (by simpa only [hs] using hB) hv

/-- At three slots and the point schedule, deadline coverage retains the
original own-payload conclusion (PROTOCOL.md `sec:healing-schedule`). -/
theorem firstDeadlineProposal_carries_roundRow_point_of_R_eq_three
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    (hR : S.hc.R = 3) {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.deadlineProposalSlot q) ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.deadlineProposalSlot q) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations := by
  rw [S.deadlineProposalSlot_eq_plusTwo_of_R_eq_three hR q] at hhor hB
  rw [WindowAction.windowActionAttestationAt_point S rho v q (hpoint v q)]
  exact plusTwoProposal_carries_resolvedRoundRow_point S hpoint adm hcar hhor hv hB
    (actionAttestationAt_mem_selectedRows_at_plusTwo_point S adm hpoint hcar hpost hhor hv)

/-- The point instance recovers own-payload carriage at the original +2
proposal, including the availability premise (PROTOCOL.md `sec:healing-schedule`). -/
theorem plusTwoProposal_carries_roundRow_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B)
    {v : V} (hv : v ∈ rho.honest) : actionAttestationAt S rho v q ∈ B.attestations :=
  plusTwoProposal_carries_resolvedRoundRow_point S hpoint adm hcar hhor hv hB
    (actionAttestationAt_mem_selectedRows_at_plusTwo_point S adm hpoint hcar hpost hhor hv)

#print axioms windowActionRow_mem_processedRows_of_deadline
#print axioms windowActionRow_mem_processedRows_at_deadline
#print axioms windowActionRow_mem_selectedRows_at_deadline
#print axioms actionAttestationAt_mem_selectedRows_at_plusTwo_point
#print axioms windowActionRow_mem_selectedRows_at_first_deadline
#print axioms proposal_covers_windowActionRow_at_deadline
#print axioms firstDeadlineProposal_covers_roundRow
#print axioms plusTwoProposal_covers_roundRow_of_R_eq_three
#print axioms firstDeadlineProposal_carries_roundRow_point_of_R_eq_three
#print axioms plusTwoProposal_carries_roundRow_point

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
