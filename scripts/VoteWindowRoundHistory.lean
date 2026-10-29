import DecoupledConsensusProofs.Protocol.Schedule.WindowAction

/-!
Counterexample to the strict-round component of
`NamedOutageProvenance.honest_held_ancestor_row_before_action` under P1/P2/P3.
The run emits a round-zero attestation at time 1 and carries it in a proposal
at time 4, before the paper action time 6. Both schedule well-formedness and
unforgeability hold, and the horizon includes time 6. This diagnostic does
not import the legacy provenance theorem or use its tracked placeholders.
-/

open DecoupledConsensusModel Protocol Execution
namespace VoteWindowRoundHistory

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


-- An early round-zero action is carried by the next proposal before a_0.
def rho : NamedRun (Fin 1) where
  honest := Finset.univ
  horizon := 6
  events := [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4, .tick 0 5, .tick 0 6]

def row : NamedAttestation (Fin 1) :=
  NamedActionReads.windowActionAttestationAt S rho 0 0

def B : NamedBlock (Fin 1) := .node .genesis 1 ⟨2⟩ [] [] [row] 0

theorem out0 : NamedRun.emittedAt S rho 0 0 0 = [] := by rfl
theorem out1 : NamedRun.emittedAt S rho 1 0 1 = [.attest row] := by rfl
theorem out2 : NamedRun.emittedAt S rho 2 0 2 = [] := by rfl
theorem out3 : NamedRun.emittedAt S rho 3 0 3 = [] := by rfl
theorem out4 : NamedRun.emittedAt S rho 4 0 4 = [.block B] := by decide +kernel

theorem out5_no_block : (NamedRun.emittedAt S rho 5 0 5).all
    (fun o => match o with | .block _ => false | _ => true) = true := by
  decide +kernel

theorem out6 : NamedRun.emittedAt S rho 6 0 6 = [] := by rfl

theorem point_covered : S.a 0 ≤ rho.horizon := by decide

theorem row_round : row.round = 0 := by rfl

theorem event_shape {i : Nat} {e : NamedEvent (Fin 1)}
    (hi : rho.events[i]? = some e) : i < 7 ∧ e = .tick 0 (i : Time) := by
  have hiLt : i < 7 := by
    simpa [rho] using (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨hiLt, ?_⟩
  interval_cases i <;> exact Option.some.inj hi.symm

theorem no_delivery {i : Nat} {v : Fin 1} {o : NamedObject (Fin 1)} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) : False := by
  have h := (event_shape hi).2
  cases h

theorem block_emission {v : Fin 1} {C : NamedBlock (Fin 1)} {t : Time}
    (hem : NamedRun.emits S rho v (.block C) t) : t = 4 ∧ C = B := by
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨hiLt, he⟩ := event_shape hi
  have ht : t = (i : Time) := congrArg NamedEvent.time he
  subst t
  interval_cases i <;> norm_num only at ho
  all_goals try simp only [out0, out1, out2, out3, out4, out6,
    List.not_mem_nil, List.mem_singleton, NamedObject.block.injEq,
    reduceCtorEq] at ho
  · exact ⟨rfl, ho⟩
  · have hfalse : false = true := List.all_eq_true.mp out5_no_block (.block C) ho
    cases hfalse

theorem in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  change e ∈ [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4, .tick 0 5, .tick 0 6] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

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
    change t ≤ 6 at hhi
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
    · obtain ⟨_, rfl⟩ := block_emission hem
      exact False.elim (List.not_mem_nil hu)
    · exact False.elim (no_delivery hi)
  carried_attest := by
    intro v C t hp a ha hh
    rcases hp with hem | ⟨i, hi⟩
    · obtain ⟨rfl, rfl⟩ := block_emission hem
      have he : a = row := by simpa only [B, NamedBlock.attestations,
        List.mem_singleton] using ha
      subst a
      refine ⟨1, by decide, 1, rfl, ?_⟩
      change NamedObject.attest row ∈ NamedRun.emittedAt S rho 1 0 1
      rw [out1]
      exact List.mem_singleton_self _
    · exact False.elim (no_delivery hi)

-- Kernel reduction checks the actual folded store; no native_decide is used.
set_option maxRecDepth 10000 in
theorem held_before_point :
    B ∈ (NamedRun.stateBeforeTime S rho (S.a 0) 0).st.bodies := by
  decide +kernel

theorem carried_current_round :
    NamedScheduleWellFormed S rho ∧ NamedUnforgeable S rho ∧
    B ∈ (NamedRun.stateBeforeTime S rho (S.a 0) 0).st.bodies ∧
    NamedBlock.Preceq B B ∧ row ∈ B.attestations ∧
    row.val_index ∈ rho.honest ∧ ¬ row.round < 0 := by
  refine ⟨schedule, authentic, held_before_point, ?_, ?_, Finset.mem_univ _, ?_⟩
  · decide +kernel
  · exact List.mem_singleton_self _
  · exact Nat.not_lt_zero _

theorem before_action_strict_round_fails :
    ¬ (NamedScheduleWellFormed S rho → NamedUnforgeable S rho →
      ∀ (reader : Fin 1) (r : Round) (C A : NamedBlock (Fin 1))
        (a : NamedAttestation (Fin 1)),
        S.a r ≤ rho.horizon →
        C ∈ (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies →
        NamedBlock.Preceq A C → a ∈ A.attestations → a.val_index ∈ rho.honest →
        a.round < r) := by
  intro h
  have hc := carried_current_round
  exact hc.2.2.2.2.2.2 (h schedule authentic 0 0 B B row point_covered
    hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1)

#print axioms carried_current_round
#print axioms before_action_strict_round_fails
end VoteWindowRoundHistory
