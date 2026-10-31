import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint
import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
import DecoupledConsensusProofs.Execution.ModelVocabulary
import DecoupledConsensusInternal.Execution.Assumptions
import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence

/-!
A fully admissible nine-tick run refutes the strict `+2` carrier exclusion.
With Δ = 1, R = 3 and act r = 12*r + 1, the round-zero row is emitted at
1 and accepted in the slot-one proposal at 4, before the slot-two proposal
at 8. The row also equals the original paper observer at 6. The slot-two
proposal has that row on its parent chain and has no own attestation rows,
as prescribed by the on-chain exclusion in §7 (`PROTOCOL.md#proposal_attestations`).

These proofs use neither CarrierFirst nor the excluded point-emission helpers.
The final negated contract instantiates every premise, including full
Admissible, ProposerCarrierAt and the horizon through the +2 proposal.
All computations used as proofs are kernel checked; no native decision
axiom is used. The sorting fact is proved separately from the finite fold.
-/
-- The finite nine-tick fold expands nested named stores during kernel reduction.
set_option maxRecDepth 20000
open DecoupledConsensusModel Protocol Execution
namespace VoteWindowEarlyCarrier

def E : Env (Fin 1) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun _ => 1, weight_pos := by intro v; decide }
def hc : HealConfig := ⟨3, by decide, 2, by decide⟩
def cfg : HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 6
  K_ge_four := by decide
  D_ge_two := by decide
def node (v : Fin 1) : Node (Fin 1) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true
  act := fun r => slotStart E.Δ (hc.opening_slot r) + 1

def S : Setup (Fin 1) where
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
    refine ⟨12 * r + 1, ?_⟩
    simp [node, E, hc, HealConfig.opening_slot, slotStart]
    ring
  timeout_rounds := by decide
  committee_nonempty := by intro s; exact ⟨0, Finset.mem_univ _⟩
  outage_window := by decide


def rho : NamedRun (Fin 1) where
  honest := Finset.univ
  horizon := 8
  events := [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4,
    .tick 0 5, .tick 0 6, .tick 0 7, .tick 0 8]
def row := NamedActionReads.windowActionAttestationAt S rho 0 0
def B : NamedBlock (Fin 1) := .node .genesis 1 ⟨2⟩ [] [] [row] 0
def B2 : NamedBlock (Fin 1) := .node B 2 ⟨3⟩ [⟨0, 1, ⟨2⟩⟩] [⟨0, 1, ⟨2⟩⟩] [] 0

theorem roots2 : NamedProposalRows.orderedRoots
    (Statements.Instantiation.proposerReadAt S rho 2).st = [⟨0⟩, ⟨2⟩] := by
  have hroots : ((Statements.Instantiation.proposerReadAt S rho 2).st.bodies.image
      NamedBlock.root) = ({⟨2⟩, ⟨0⟩} : Finset BlockId) := by decide +kernel
  unfold NamedProposalRows.orderedRoots
  rw [hroots]
  rw [Finset.pair_comm]
  rw [Finset.sort_insert (fun a b : BlockId => a ≤ b) (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; decide)
    (by decide), Finset.sort_singleton]
theorem rows2 : NamedProposalRows.select .poolAndCarried S.hc
    (Statements.Instantiation.proposerReadAt S rho 2).st = [row, row] := by
  unfold NamedProposalRows.select NamedProposalRows.carriedRows NamedProposalRows.orderedBodies
  rw [roots2]
  decide +kernel

theorem parent2 : NamedActions.parentBody?
    (Statements.Instantiation.proposerReadAt S rho 2).st
    (proposal_input_with
      (NamedProfile.gradeContract (Statements.Instantiation.proposerReadAt S rho 2).cache)
      S.E S.hc (S.node 0)
      (Statements.Instantiation.proposerReadAt S rho 2).st.core.toHealing).parent = some B := by
  decide +kernel
theorem proposal2 : Statements.Instantiation.proposedBlockAt S rho 2 = some B2 := by
  unfold Statements.Instantiation.proposedBlockAt
  dsimp only
  have hp : S.E.proposer 2 = 0 := rfl
  rw [hp, Proofs.NamedActions.proposal_eq_of_parent _ .poolAndCarried _ _ _ _ B parent2]
  simp only [rows2]
  decide +kernel

theorem proposal_duty2 :
    NamedDuties.propose_block_with
      (NamedProfile.gradeContract (onPhaseTick S.E S.hc
        (NamedRun.stateBefore S rho 8 0).st.core.toHealing 8
        (NamedRun.stateBefore S rho 8 0).cache))
      S.E S.hc S.cfg (S.node 0)
      (NamedStore.setClock S.E (NamedRun.stateBefore S rho 8 0).st 8) =
      (NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
        (NamedStore.setClock S.E (NamedRun.stateBefore S rho 8 0).st 8) B2, some B2) := by
  have hp : NamedActions.proposal_with
      (NamedProfile.gradeContract (onPhaseTick S.E S.hc
        (NamedRun.stateBefore S rho 8 0).st.core.toHealing 8
        (NamedRun.stateBefore S rho 8 0).cache))
      .poolAndCarried S.E S.hc (S.node 0)
      (NamedStore.setClock S.E (NamedRun.stateBefore S rho 8 0).st 8) = some B2 := by
    exact proposal2
  unfold NamedDuties.propose_block_with
  rw [hp]

theorem out8 : NamedRun.emittedAt S rho 8 0 8 = [.block B2] := by
  change (NamedNode.tick S 0 (NamedRun.stateBefore S rho 8 0) 8).2 = _
  unfold NamedNode.tick NamedProfile.tick
  dsimp only
  rw [Proofs.NamedTick.tick_computed_duties]
  dsimp only
  rw [proposal_duty2]
  decide +kernel

theorem outputs :
    NamedRun.emittedAt S rho 0 0 0 = [] ∧
    NamedRun.emittedAt S rho 1 0 1 = [.attest row] ∧
    NamedRun.emittedAt S rho 2 0 2 = [] ∧
    NamedRun.emittedAt S rho 3 0 3 = [] ∧
    NamedRun.emittedAt S rho 4 0 4 = [.block B] ∧
    NamedRun.emittedAt S rho 6 0 6 = [] ∧
    NamedRun.emittedAt S rho 7 0 7 = [] ∧
    NamedRun.emittedAt S rho 8 0 8 = [.block B2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, out8⟩ <;> decide +kernel

theorem no_block5 : (NamedRun.emittedAt S rho 5 0 5).all
    (fun o => match o with | .block _ => false | _ => true) = true := by decide +kernel

theorem body2 : B2.parent = B ∧ B2.root = ⟨3⟩ ∧ B2.attestations = [] ∧
    B2.gf_votes.all (fun u => decide (.gfVote u ∈ NamedRun.emittedAt S rho 5 0 5)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem exact_paper_row : row = Proofs.HealingSurface.actionAttestationAt S rho 0 0 := by
  decide +kernel

theorem accepted_early : NamedRun.acceptsAt S rho 4 0 (.block B) 4 := by
  refine ⟨⟨Or.inl ⟨4, rfl, ?_⟩, ⟨.tick 0 4, rfl, rfl, rfl⟩⟩, ?_, ?_⟩
  · rw [outputs.2.2.2.2.1]; exact List.mem_singleton_self _
  · decide +kernel
  · decide +kernel

theorem event_shape {i : Nat} {e : NamedEvent (Fin 1)}
    (hi : rho.events[i]? = some e) : i < 9 ∧ e = .tick 0 (i : Time) := by
  have hiLt : i < 9 := by simpa [rho] using (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨hiLt, ?_⟩
  interval_cases i <;> exact Option.some.inj hi.symm

theorem no_delivery {i : Nat} {v : Fin 1} {o : NamedObject (Fin 1)} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) : False := by
  have h := (event_shape hi).2
  cases h

theorem block_emission {v : Fin 1} {C : NamedBlock (Fin 1)} {t : Time}
    (hem : NamedRun.emits S rho v (.block C) t) :
    (t = 4 ∧ C = B) ∨ (t = 8 ∧ C = B2) := by
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨hiLt, he⟩ := event_shape hi
  have ht : t = (i : Time) := congrArg NamedEvent.time he
  subst t
  rcases outputs with ⟨h0, h1, h2, h3, h4, h6, h7, h8⟩
  interval_cases i <;> norm_num only at ho
  all_goals try simp only [h0, h1, h2, h3, h4, h6, h7, h8,
    List.not_mem_nil, List.mem_singleton, NamedObject.block.injEq, reduceCtorEq] at ho
  · exact Or.inl ⟨rfl, ho⟩
  · have hfalse : false = true := List.all_eq_true.mp no_block5 (.block C) ho
    cases hfalse
  · exact Or.inr ⟨rfl, ho⟩

theorem in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  change e ∈ [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4,
    .tick 0 5, .tick 0 6, .tick 0 7, .tick 0 8] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem schedule : NamedScheduleWellFormed S rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := in_horizon
  honest_only := by intro e he; exact Finset.mem_univ _
  tick_public := by
    intro v t ht
    have hlo : 0 ≤ t := (in_horizon _ ht).1
    refine ⟨t.toNat, ?_⟩
    change t = (t.toNat : Int) * 1
    rw [mul_one, Int.toNat_of_nonneg hlo]
  tick_total := by
    intro v hv t ht hlo hhi
    change t ≤ 8 at hhi
    interval_cases t <;> fin_cases v <;> decide

theorem authentic : NamedUnforgeable S rho where
  unforgeable := by
    intro v o t hp u hu ha
    rcases hp with hem | ⟨i, hi⟩
    · have hv : v = u := Subsingleton.elim _ _
      exact ⟨t, le_rfl, hv ▸ hem⟩
    · exact False.elim (no_delivery hi)
  carried_gf := by
    intro v C t hp u hu hh
    rcases hp with hem | ⟨i, hi⟩
    · rcases block_emission hem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (List.not_mem_nil hu)
      · have ho := of_decide_eq_true (List.all_eq_true.mp body2.2.2.2 u hu)
        have hv : u.val_index = 0 := Subsingleton.elim _ _
        exact ⟨5, by decide, 5, by rw [hv]; rfl, by rw [hv]; exact ho⟩
    · exact False.elim (no_delivery hi)
  carried_attest := by
    intro v C t hp a ha hh
    rcases hp with hem | ⟨i, hi⟩
    · rcases block_emission hem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have he : a = row := by simpa only [B, NamedBlock.attestations, List.mem_singleton] using ha
        subst a
        refine ⟨1, by decide, 1, rfl, ?_⟩
        change NamedObject.attest row ∈ NamedRun.emittedAt S rho 1 0 1
        rw [outputs.2.1]; exact List.mem_singleton_self _
      · rw [body2.2.2.1] at ha
        exact False.elim (List.not_mem_nil ha)
    · exact False.elim (no_delivery hi)

theorem bodies9 : (NamedRun.stateBefore S rho 9 0).st.bodies ⊆ {NamedBlock.genesis, B, B2} := by
  change (NamedNode.tick S 0 (NamedRun.stateBefore S rho 8 0) 8).1.st.bodies ⊆ _
  unfold NamedNode.tick NamedProfile.tick
  dsimp only
  rw [Proofs.NamedTick.tick_computed_duties]
  dsimp only
  rw [proposal_duty2]
  decide +kernel

theorem bodies_table : ∀ i : Fin 10,
    (NamedRun.stateBefore S rho i 0).st.bodies ⊆ {NamedBlock.genesis, B, B2} := by
  intro i
  fin_cases i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact bodies9

theorem held_cases (i : Nat) (v : Fin 1) {D : NamedBlock (Fin 1)}
    (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies) : D = .genesis ∨ D = B ∨ D = B2 := by
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hmem : D ∈ ({NamedBlock.genesis, B, B2} : Finset _) := by
    by_cases hi : i < 10
    · exact bodies_table ⟨i, hi⟩ hD
    · have hlen : rho.events.length ≤ i := by change 9 ≤ i; omega
      have heq : NamedRun.stateBefore S rho i 0 = NamedRun.stateBefore S rho 9 0 := by
        unfold NamedRun.stateBefore
        rw [List.take_of_length_le hlen]
        rfl
      rw [heq] at hD
      exact bodies_table ⟨9, by decide⟩ hD
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem ancestor_cases {A D : NamedBlock (Fin 1)}
    (hD : D = .genesis ∨ D = B ∨ D = B2) (hAD : NamedBlock.Preceq A D) :
    A = .genesis ∨ A = B ∨ A = B2 := by
  have hB (h : NamedBlock.Preceq A B) : A = .genesis ∨ A = B ∨ A = B2 := by
    simp only [B, NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  rcases hD with rfl | rfl | rfl
  · simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using Or.inl hAD
  · exact hB hAD
  · cases he : B2 with
    | genesis =>
        have hr := body2.2.1
        rw [he] at hr
        cases hr
    | node parent slot root votes support rows proposer =>
        have hp : parent = B := by simpa only [he, NamedBlock.parent] using body2.1
        rw [he] at hAD
        simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
          decide_eq_true_eq] at hAD
        rcases hAD with hself | hparent
        · exact Or.inr (Or.inr hself)
        · simpa only [he] using hB (hp ▸ hparent)

theorem run_cases {A : NamedBlock (Fin 1)} (hA : NamedRun.blockInRun S rho A) :
    A = .genesis ∨ A = B ∨ A = B2 := by
  obtain ⟨D, hD, hAD⟩ := hA
  apply ancestor_cases (D := D) ?_ hAD
  rcases hD with hobj | ⟨v, _, i, hmem⟩
  · simp [NamedRun.objects, rho, NamedEvent.object?] at hobj
  · exact held_cases i v hmem

theorem roots : NamedRootCollisionFree S rho where
  root_injective X Y hX hY A D hAX hDY heq := by
    have ha := hAX.elim (ancestor_cases (run_cases hX)) (ancestor_cases (run_cases hY))
    have hd := hDY.elim (ancestor_cases (run_cases hX)) (ancestor_cases (run_cases hY))
    rcases ha with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
    all_goals try rfl
    all_goals have h0 : (NamedBlock.genesis : NamedBlock (Fin 1)).root = ⟨0⟩ := rfl
    all_goals have h1 : B.root = ⟨2⟩ := rfl
    all_goals simp only [h0, h1, body2.2.1, BlockId.mk.injEq] at heq
    all_goals cases heq

theorem actual_handles_self {i : Nat} {o : NamedObject (Fin 1)} {t : Time}
    (hi : rho.events[i]? = some (.tick 0 t))
    (ho : o ∈ NamedRun.emittedAt S rho i 0 t) :
    NamedRun.actualHandlesAt S rho i 0 o t := by
  refine ⟨?_, ⟨.tick 0 t, hi, rfl, rfl⟩⟩
  cases o with
  | block B => exact Or.inl ⟨t, hi, ho⟩
  | gfVote u => exact Or.inl (Or.inl ⟨t, hi, ho⟩)
  | attest a => exact Or.inl (Or.inl ⟨t, hi, ho⟩)

theorem synchrony : NamedSynchrony S rho where
  broadcast := by
    intro v hv o t hem w hw hdeadline hguard
    have hv0 : v = 0 := Subsingleton.elim _ _
    have hw0 : w = 0 := Subsingleton.elim _ _
    subst v
    subst w
    obtain ⟨i, hi, ho⟩ := hem
    have ht : 0 ≤ t := (in_horizon _ (List.mem_of_getElem? hi)).1
    refine ⟨t, le_rfl, ?_, i, actual_handles_self hi ho⟩
    change t < max t 0 + 1
    rw [max_eq_left ht]
    exact lt_add_of_pos_right t (by decide)
  relay_block := by
    intro v hv i C t hacc w hw hmiss _ _
    have heq : w = v := Subsingleton.elim _ _
    subst w
    rw [hacc.2.2] at hmiss
    cases hmiss
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmiss _ _
    have heq : w = v := Subsingleton.elim _ _
    subst w
    rw [hacc.2.2] at hmiss
    cases hmiss
  relay_attest := by
    intro v hv i a t hacc w hw hmiss _ _
    have heq : w = v := Subsingleton.elim _ _
    subst w
    rw [hacc.2.2] at hmiss
    cases hmiss

theorem admissible : Admissible S rho where
  toNamedScheduleWellFormed := schedule
  toNamedDeliveryWellFormed := {
    wire := by intro i v o t hi; exact False.elim (no_delivery hi)
    deps := by intro i v o t hi; exact False.elim (no_delivery hi)
    fresh := by intro i v o t hi; exact False.elim (no_delivery hi) }
  toNamedRootCollisionFree := roots
  toNamedUnforgeable := authentic
  toNamedSynchrony := synchrony
  all_awake := by intros; rfl

theorem carrier_premises :
    Admissible S rho ∧ Internal.ProposerCarrierAt S rho 0 ∧
    proposal_time S.E (S.hc.opening_slot 0 + 2) ≤ rho.horizon ∧
    NamedRun.acceptsAt S rho 4 0 (.block B) 4 ∧
    4 < proposal_time S.E (S.hc.opening_slot 0 + 2) ∧
    (0 : Fin 1) ∈ rho.honest ∧
    Proofs.HealingSurface.actionAttestationAt S rho 0 0 ∈ B.attestations := by
  refine ⟨admissible, ⟨Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _⟩,
    by decide, accepted_early, by decide, Finset.mem_univ _, ?_⟩
  rw [← exact_paper_row]
  exact List.mem_singleton_self _

theorem noEarlierCarrier_contract_fails :
    ¬ (Admissible S rho → ∀ q : Round, Internal.ProposerCarrierAt S rho q →
      proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon →
      ∀ (reader : Fin 1) (i : Nat) (C : NamedBlock (Fin 1)) (t : Time),
        NamedRun.acceptsAt S rho i reader (.block C) t →
        t < proposal_time S.E (S.hc.opening_slot q + 2) →
        ∀ v ∈ rho.honest, Proofs.HealingSurface.actionAttestationAt S rho v q ∈
          C.attestations → False) := by
  intro h
  obtain ⟨hadm, hcar, hhor, hacc, ht, hv, ha⟩ := carrier_premises
  exact h hadm 0 hcar hhor 0 4 B 4 hacc ht 0 hv ha

theorem plusTwo_row_placement :
    Proofs.HealingSurface.actionAttestationAt S rho 0 0 ∈
      NamedProposalRows.chainRows B2.parent ∧
    Proofs.HealingSurface.actionAttestationAt S rho 0 0 ∉ B2.attestations := by
  rw [← exact_paper_row]
  simp [B2, B, NamedBlock.parent, NamedBlock.attestations, NamedProposalRows.chainRows]

#print axioms plusTwo_row_placement
#print axioms noEarlierCarrier_contract_fails
#print axioms carrier_premises
#print axioms exact_paper_row
#print axioms accepted_early
end VoteWindowEarlyCarrier
