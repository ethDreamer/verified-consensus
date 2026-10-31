module
public import DecoupledConsensusProofs.Protocol.Schedule.DeadlineProposal
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence
public import DecoupledConsensusStatements.Instantiation

/-!
# Honest proposal gaps after the row deadline

Strong recurrence supplies a triple and two preceding honest openings, not
an honest proposal immediately after that triple. This schedule witnesses
the distinction for four-slot rounds and a one-round row window
(PROTOCOL.md `sec:healing-schedule`, `proposal_attestations`).

The results concern the exact recurrence predicates and proposal clock only.
The empty event list below is not an admissible execution, and these results
do not assert a counterexample to a consensus or finality theorem.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.CarrierDeadlineGap
open Protocol Execution
open Statements.Instantiation

/-- Honest proposal slots in a four-round periodic schedule. -/
def honestSlot (s : Slot) : Prop := s % 16 ∈ ([0, 4, 8, 9, 10] : List Nat)
instance (s : Slot) : Decidable (honestSlot s) := inferInstanceAs
  (Decidable (s % 16 ∈ ([0, 4, 8, 9, 10] : List Nat)))

/-- One honest identity with weight three and one faulty identity with weight
one; committees contain only the honest identity. -/
def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun s => if honestSlot s then 0 else 1
  committees := ⟨fun _ => {0}⟩
  electorate :=
    { weight := fun v => if v = 0 then 3 else 1
      weight_pos := by intro v; split <;> decide }

/-- Four slots per round, with the minimum permitted row window. -/
def hc : HealConfig := ⟨4, by decide, 1, by decide⟩

/-- Gap six is within the permitted K bound; timeout is exactly two rounds. -/
def cfg : HeightConfig := ⟨8, 2, 8, by decide, by decide⟩

/-- Actions occur after the triple and before the P2 deadline. -/
def node (v : Fin 2) : Node (Fin 2) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true
  act := fun r => slotStart E.Δ (hc.opening_slot r) + 9

/-- The schedule satisfies all structural Setup conditions, including P1–P3. -/
def S : Setup (Fin 2) where
  E := E
  hc := hc
  cfg := cfg
  node := node
  node_val_index := by intro v; rfl
  act_post_completion := by
    intro v r
    simp [node, domain, Phase.domainOffset, opening, proposal_time, Env.t, E]
  act_before_round_end := by
    intro v r
    simp [node, opening, proposal_time, Env.t, E, hc, HealConfig.opening_slot, slotStart]
    nlinarith
  act_pre_cutoff := by
    intro v r
    simp [node, early, Phase.earlyOffset, opening, proposal_time, Env.t, E,
      hc, HealConfig.opening_slot, slotStart]
    nlinarith
  act_public := by
    intro v r
    refine ⟨16 * r + 9, ?_⟩
    simp [node, E, hc, HealConfig.opening_slot, slotStart]
    ring
  timeout_rounds := by decide
  committee_nonempty := by intro s; exact ⟨0, Finset.mem_singleton_self _⟩
  outage_window := by decide

/-- A carrier for schedule predicates only; no execution validity is claimed. -/
def rho : Run (Fin 2) where
  honest := {0}
  horizon := 1000
  events := []

private theorem proposer_honest_iff (s : Slot) :
    S.E.proposer s ∈ rho.honest ↔ honestSlot s := by
  change (if honestSlot s then (0 : Fin 2) else 1) ∈ ({0} : Finset (Fin 2)) ↔ _
  split <;> simp_all

/-- Every four-round period has the triple at its third opening. -/
theorem openingCarrier (n : Nat) :
    Internal.ProposerOpeningCarrierAt S rho (4 * n + 2) := by
  simp only [Internal.ProposerOpeningCarrierAt, Internal.ProposerCarrierAt]
  simp only [proposer_honest_iff]
  simp only [S, hc, HealConfig.opening_slot, honestSlot,
    List.mem_cons, List.not_mem_nil, or_false]
  dsimp only [Slot, Round] at *
  omega

/-- The exact internal strong recurrence holds with gap six. -/
theorem openingCarrierRecurrence : Internal.ProposerOpeningCarrierRecurrence S rho 6 := by
  intro k _ _
  change Nat at k
  refine ⟨4 * (k / 4 + 1) + 2, ?_, ?_, openingCarrier _⟩ <;>
    dsimp only [Round] at * <;> omega

/-- The protected interface's continuous-time strong recurrence also holds;
the schedule gap is not an artifact of round-sampled recurrence. -/
theorem strongRecurrence : Statements.Generic.StrongMultiProposerRecurrence
    (interface S) (constants S) rho 0 6 := by
  intro t ht _
  change Int at t
  let n := t.toNat / 64 + 1
  have htcast : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  have hnlo : t + 32 ≤ (64 * n + 32 : Nat) := by
    dsimp only [n]
    omega
  have hnhi : ((64 * n + 32 : Nat) : Int) ≤ t + 96 := by
    dsimp only [n]
    omega
  refine ⟨(4 * n + 2) * 4, ?_, ?_, ?_, ?_⟩
  · change t + 2 * 16 ≤ 4 * 1 * (((4 * n + 2) * 4 : Nat) : Int)
    push_cast at hnlo ⊢
    linarith
  · change 4 * 1 * (((4 * n + 2) * 4 : Nat) : Int) ≤ t + 6 * 16
    push_cast at hnhi ⊢
    linarith
  · refine ⟨⟨4 * n + 2, rfl⟩, ?_⟩
    intro j hj
    change Nat at j
    change j < 3 at hj
    rw [show (interface S).proposer = S.E.proposer from rfl, proposer_honest_iff]
    simp only [honestSlot, List.mem_cons, List.not_mem_nil, or_false]
    dsimp only [Slot, Round] at *
    omega
  · intro s hs hlo hhi
    obtain ⟨r, rfl⟩ := hs
    change Nat at r
    change 4 * 1 * (((4 * n + 2) * 4 : Nat) : Int) - 2 * 16 ≤
      4 * 1 * ((r * 4 : Nat) : Int) at hlo
    change 4 * 1 * ((r * 4 : Nat) : Int) <
      4 * 1 * (((4 * n + 2) * 4 : Nat) : Int) at hhi
    change S.E.proposer (r * 4) ∈ rho.honest
    rw [proposer_honest_iff]
    simp only [honestSlot, List.mem_cons, List.not_mem_nil, or_false]
    push_cast at hlo hhi
    have hr : r = 4 * n ∨ r = 4 * n + 1 := by omega
    rcases hr with rfl | rfl <;> dsimp only [Slot, Round] at * <;> omega

/-- Round two's triple is honest, but every eligible post-deadline proposal
is faulty. The next honest proposal is the round-four opening. -/
theorem no_eligible_honest_proposal :
    Internal.ProposerCarrierAt S rho 2 ∧
    S.deadlineProposalSlot 2 = 11 ∧
    S.E.proposer 16 ∈ rho.honest ∧
    ∀ s : Slot, early S.E S.hc 3 .g2 ≤ proposal_time S.E s →
      S.hc.round_of s - S.hc.η_SG ≤ 2 → S.E.proposer s ∉ rho.honest := by
  refine ⟨(openingCarrier 0).2.2, rfl, ?_, ?_⟩
  · decide
  · intro s hdeadline helig
    change Nat at s
    rw [proposer_honest_iff]
    change (43 : Int) ≤ 4 * 1 * (s : Int) at hdeadline
    change s / 4 - 1 ≤ 2 at helig
    simp only [honestSlot, List.mem_cons, List.not_mem_nil, or_false]
    dsimp only [Slot, Round] at *
    omega

/-- At any honest proposal after round two's deadline, the protocol's row
filter rejects round two, independently of the pool contents
(PROTOCOL.md `proposal_attestations`). -/
theorem expired_at_honest_proposal (st : Store (Fin 2))
    (hdeadline : early S.E S.hc 3 .g2 ≤ proposal_time S.E st.s)
    (hhonest : S.E.proposer st.s ∈ rho.honest) :
    ProposalRows.inWindow S.hc st 2 = false := by
  unfold ProposalRows.inWindow
  rw [decide_eq_false_iff_not]
  intro helig
  exact no_eligible_honest_proposal.2.2.2 st.s hdeadline helig.1 hhonest

#print axioms openingCarrierRecurrence
#print axioms strongRecurrence
#print axioms no_eligible_honest_proposal
#print axioms expired_at_honest_proposal
end DecoupledConsensusModel.Proofs.CarrierDeadlineGap
