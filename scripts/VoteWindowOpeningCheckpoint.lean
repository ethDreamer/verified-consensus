import DecoupledConsensusProofs.Execution.CarrierCoverage
import DecoupledConsensusProofs.Protocol.ChainState.W4NamedJustificationMonotone
import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint
import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
import DecoupledConsensusProofs.Execution.ModelVocabulary
import DecoupledConsensusInternal.Execution.Assumptions
import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence

/-!
The first-carrier target-row obligation needs more than timely carriage.
The checked local chain below has an opening at height 2, an actual-shaped
row targeting height 1, and a common carrier that finalizes height 1 without
justifying height 2. No additional accumulator premise is assumed.

The executable probe uses public ticks 0 through 38. Validator 0 has weight
3 and is the only honest validator; validator 1 has weight 1, is silent, and
is proposer only at slots 4 and 5. Round 2 acts at time 25; other rounds use
the point schedule. It prints actual/paper height pairs, opening height,
carrier justification/finality heights, row membership, and the justification
heights of proposal observers through the confirmation deadline.

Setup arithmetic and the local chain lemmas are kernel checked. The #eval
output is an executable probe, NOT a kernel proof of its values. This file
does not prove Admissible or CanonicalRegimeRoundAt for the finite run and is
not a counterexample to a protected theorem.
-/
set_option maxRecDepth 20000
open DecoupledConsensusModel Protocol Execution
namespace VoteWindowOpeningCheckpoint

def E : Env (Fin 2) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun s => if s = 4 ∨ s = 5 then 1 else 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by intro v; split_ifs <;> decide }
def hc : HealConfig := ⟨3, by decide, 2, by decide⟩
def cfg : HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 6
  K_ge_four := by decide
  D_ge_two := by decide
def node (v : Fin 2) : Node (Fin 2) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true
  act := fun r => slotStart E.Δ (hc.opening_slot r) + (if r = 2 then 1 else 6)

def S : Setup (Fin 2) where
  E := E
  hc := hc
  cfg := cfg
  node := node
  node_val_index := by intro v; rfl
  act_post_completion := by
    intro v r
    by_cases hr : r = 2 <;> simp [node, domain, Phase.domainOffset, opening, proposal_time, Env.t, E, hr]
  act_before_round_end := by
    intro v r
    simp [node, opening, proposal_time, Env.t, E, hc, HealConfig.opening_slot, slotStart]
    split_ifs <;> nlinarith
  act_pre_cutoff := by
    intro v r
    simp [node, early, Phase.earlyOffset, opening, proposal_time, Env.t, E,
      hc, HealConfig.opening_slot, slotStart]
    split_ifs <;> nlinarith
  act_public := by
    intro v r
    refine ⟨12 * r + (if r = 2 then 1 else 6), ?_⟩
    simp [node, E, hc, HealConfig.opening_slot, slotStart]
    ring
  timeout_rounds := by decide
  committee_nonempty := by intro s; exact ⟨0, Finset.mem_univ _⟩
  outage_window := by decide


def rho : NamedRun (Fin 2) where
  honest := {0}
  horizon := 38
  events := (List.range 39).map (fun i => .tick 0 (i : Time))
def proposal (s : Slot) : NamedBlock (Fin 2) :=
  (Statements.Instantiation.proposedBlockAt S rho s).getD .genesis

def row := NamedActionReads.windowActionAttestationAt S rho 0 2

/-- The emitter already confirmed this height-one prefix. -/
def prior : NamedBlock (Fin 2) := .node .genesis 3 ⟨4⟩ [] [] [] 0

def firstRow : NamedAttestation (Fin 2) where
  val_index := 0
  round := 1
  confirmed := some ⟨4⟩
  height_pair := .vote 1 ⟨0⟩ false
  finality_pair := none

def earlyRow : NamedAttestation (Fin 2) where
  val_index := 0
  round := 2
  confirmed := some ⟨4⟩
  height_pair := .vote 1 ⟨0⟩ false
  finality_pair := some ⟨1, ⟨0⟩⟩

def openingBlock : NamedBlock (Fin 2) := .node prior 6 ⟨7⟩ [] [] [firstRow] 0

def commonCarrier : NamedBlock (Fin 2) := .node openingBlock 7 ⟨8⟩ [] [] [earlyRow] 0

/-- The original triple is honest and R=3 supplies the carrier time bound. -/
theorem carrier_schedule : Internal.ProposerCarrierAt S rho 2 ∧
    (∀ v r, (S.node v).act r + S.E.Δ ≤ proposal_time S.E (S.hc.opening_slot r + 2)) ∧
    (S.node 0).act 2 < confirmation_time S.E (S.hc.opening_slot 2) := by
  refine ⟨?_, ?_, by decide⟩
  · unfold Internal.ProposerCarrierAt
    decide +kernel
  · intro v r
    exact Proofs.HealingSurface.carrier_bound_of_R_eq_three S rfl r v

/-- In this schedule the authorized carriage seam follows from admissibility;
the early-input question is distinct from availability. This theorem does not
assert that the executable probe has been proved admissible. -/
theorem coverage_if_admissible (adm : Admissible S rho) :
    Proofs.HealingSurface.CarrierCoverage S rho 2 :=
  Proofs.HealingSurface.carrierCoverage_of_R_eq_three S adm rfl
    carrier_schedule.1 (by decide) (by decide)

/-- Carriage and positive progress at the older checkpoint do not justify the
opening's new height. The row is in the carrier's own payload. -/
theorem local_checkpoint_gap :
    (derive_named S.E S.cfg openingBlock).h = 2 ∧
    (derive_named S.E S.cfg openingBlock).nj = false ∧
    earlyRow ∈ commonCarrier.attestations ∧
    (derive_named S.E S.cfg commonCarrier).h_j = 1 ∧
    (derive_named S.E S.cfg commonCarrier).h_F = 1 ∧
    earlyRow.height_pair ≠ .vote (derive_named S.E S.cfg openingBlock).h
      (derive_named S.E S.cfg openingBlock).T_h.root false := by decide +kernel

/-- The already-justified alternative at the opening height is absent from
this local carrier chain. -/
theorem no_opening_height_justification :
    ¬ ∃ X : NamedBlock (Fin 2), NamedBlock.Preceq X commonCarrier ∧
      (derive_named S.E S.cfg X).h_j = (derive_named S.E S.cfg openingBlock).h := by
  rintro ⟨X, hX, hh⟩
  have hmono := Proofs.HealingSurface.namedJustification_le_of_preceq S.E S.cfg hX
  rw [hh, local_checkpoint_gap.1, local_checkpoint_gap.2.2.2.1] at hmono
  exact (by decide : ¬ (2 : Nat) ≤ 1) hmono

/-- The missing plateau at the live-height bridge is not supplied by ancestry.
The source and parent are on the same chain, but the opening advanced height. -/
theorem source_parent_height_gap :
    NamedBlock.Preceq prior commonCarrier.parent ∧
    (derive_named S.E S.cfg prior).h = 1 ∧
    (derive_named S.E S.cfg commonCarrier.parent).h = 2 ∧
    earlyRow.height_pair = .vote (derive_named S.E S.cfg prior).h
      (derive_named S.E S.cfg prior).T_h.root false := by decide +kernel

#print axioms carrier_schedule
#print axioms coverage_if_admissible
#print axioms local_checkpoint_gap
#print axioms no_opening_height_justification
#print axioms source_parent_height_gap

#eval (row.height_pair,
  (Proofs.HealingSurface.actionAttestationAt S rho 0 2).height_pair,
  (derive_named S.E S.cfg (proposal 6)).h,
  (derive_named S.E S.cfg (proposal 7)).h_j,
  (derive_named S.E S.cfg (proposal 7)).h_F,
  decide (row ∈ (proposal 7).attestations),
  (List.range 10).map (fun s => (derive_named S.E S.cfg (proposal s)).h_j))

#eval (Proofs.HealingSurface.actionFGSource S
  (Execution.NamedActionReads.actionReadAt S rho 0 2) == some (proposal 6).erase)

end VoteWindowOpeningCheckpoint
