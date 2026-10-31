module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryBoundary
public import DecoupledConsensusProofs.Execution.FGSelectorWitness
public import DecoupledConsensusProofs.Protocol.ValidatorClient.WindowRecoveryInput

@[expose] public section

/-! # Named prefix-record recovery boundary
The retained prefix-record induction uses actual emitted action rows.
The record fields remain in `NamedRecord.legacy`, while every action row and
every chain-state argument uses `NamedAttestation` and `derive_named`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol
open Protocol
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest named record has no recovery-height lock in a capped prefix. -/
theorem stateBefore_lock_none_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) :
    ∀ n : Nat, n ≤ stop →
      (rho.stateBefore S n v).record.legacy.lock blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
        NamedNode.initial, Protocol.NamedRecord.initial,
        Protocol.Record.initial]
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      have hstep : rho.stateBefore S (n + 1) =
          (rho.events[n]?.toList).foldl (World.step S)
            (rho.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hevent : rho.events[n]? with _ | e
      · rw [hstep, hevent]
        simpa only [Option.toList, List.foldl_nil] using ihN
      · cases e with
        | deliver u o t =>
            by_cases huv : u = v
            · subst u
              rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_self]
              simpa only [NamedNode.process_record_eq] using ihN
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN
        | tick u t =>
            by_cases huv : u = v
            · subst u
              have hrecord : (rho.stateBefore S (n + 1) v).record =
                  (on_tick_emit S v (rho.stateBefore S n v) t).1.record :=
                stateBefore_succ_record S rho hevent
              cases hpost :
                  (rho.stateBefore S (n + 1) v).record.legacy.lock blocked with
              | none => rfl
              | some T =>
                  have hpostTick :
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.lock
                          blocked = some T := by
                    rw [← hrecord]
                    exact hpost
                  obtain ⟨a, hemitted, hpair⟩ :=
                    Protocol.on_tick_emit_lock_introduced
                      S v (rho.stateBefore S n v) t ihN hpostTick
                  have hemit : rho.emits S v (Object.attest a) t :=
                    ⟨n, hevent, hemitted⟩
                  exact False.elim (WindowRecoveryInput.finality_height_ne S adm
                    hcap hrec (Nat.lt_of_succ_le hnSuccStop) hv hevent hemitted hpair)
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN


/-- An honest named record has no proper target at the recovery height in a
capped prefix. This is the named prefix-record induction retained in the prior
`RecoveryBoundaryRun` Open record. -/
theorem stateBefore_target_none_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) :
    ∀ n : Nat, n ≤ stop →
      (rho.stateBefore S n v).record.legacy.target blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
        NamedNode.initial, Protocol.NamedRecord.initial,
        Protocol.Record.initial]
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      have hstep : rho.stateBefore S (n + 1) =
          (rho.events[n]?.toList).foldl (World.step S)
            (rho.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hevent : rho.events[n]? with _ | e
      · rw [hstep, hevent]
        simpa only [Option.toList, List.foldl_nil] using ihN
      · cases e with
        | deliver u o t =>
            by_cases huv : u = v
            · subst u
              rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_self]
              simpa only [NamedNode.process_record_eq] using ihN
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN
        | tick u t =>
            by_cases huv : u = v
            · subst u
              have hrecord : (rho.stateBefore S (n + 1) v).record =
                  (on_tick_emit S v (rho.stateBefore S n v) t).1.record :=
                stateBefore_succ_record S rho hevent
              cases hpost :
                  (rho.stateBefore S (n + 1) v).record.legacy.target blocked with
              | none => rfl
              | some T =>
                  have hpostTick :
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.target
                          blocked = some T := by
                    rw [← hrecord]
                    exact hpost
                  obtain ⟨a, hemitted, hpair⟩ :=
                    Protocol.on_tick_emit_target_introduced
                      S v (rho.stateBefore S n v) t ihN hpostTick
                  have hemit : rho.emits S v (Object.attest a) t :=
                    ⟨n, hevent, hemitted⟩
                  have hlock := stateBefore_lock_none_recoveryHeight_named
                    S adm hcap hrec hv n hnStop
                  exact False.elim (WindowRecoveryInput.target_impossible S adm
                    hcap hrec (Nat.lt_of_succ_le hnSuccStop) hv hevent hemitted
                    ihN hlock hpair)
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN

/-- The action at a capped recovery height emits a named timeout, including
the repeated-timeout record case. -/
theorem actionAttestationAt_height_pair_timeout_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (haction : strictEventIndex rho (S.a r) ≤ stop)
    {Q : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some Q)
    (hheight : ((actionStoreAt S rho v r).st.core.σ Q).h = blocked) :
    (actionAttestationAt S rho v r).height_pair =
      NamedHeightPair.vote blocked
        ((actionStoreAt S rho v r).st.core.σ Q).T_h.root true := by
  let actionPrefix := strictEventIndex rho (S.a r)
  have hstateWorld := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hstate : rho.stateBefore S actionPrefix v =
      rho.stateBeforeTime S (S.a r) v :=
    congrFun hstateWorld.symm v
  have hcapAction : HonestPrefixFinalityCap S rho actionPrefix hF0 :=
    honestPrefixFinalityCap_of_le S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed haction hcap
  have huniverse : HonestPrefixNJUniverse S rho actionPrefix blocked :=
    honestPrefixNJUniverse_of_finalityCap S
      adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed hcapAction hrec
  have htarget :
      (rho.stateBeforeTime S (S.a r) v).record.legacy.target blocked = none := by
    rw [← congrArg (fun st => st.record) hstate]
    exact stateBefore_target_none_recoveryHeight_named
      S adm hcap hrec hv actionPrefix haction
  have hlock :
      (rho.stateBeforeTime S (S.a r) v).record.legacy.lock blocked = none := by
    rw [← congrArg (fun st => st.record) hstate]
    exact stateBefore_lock_none_recoveryHeight_named
      S adm hcap hrec hv actionPrefix haction
  cases ht : (rho.stateBeforeTime S (S.a r) v).record.legacy.timeout blocked with
  | false =>
      exact actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverse
        S adm huniverse hv hstate hsource hheight ⟨htarget, ht, hlock⟩
  | true =>
      exact actionAttestationAt_height_pair_timeout_of_recorded
        S rho hsource hheight ht

/-- A proper honest target row cannot use a capped recovery height. -/
theorem honestEmittedTarget_height_ne_recovery_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {blocked hF0 h : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {a : NamedAttestation V} {ta : Time} {root : BlockId}
    (ha : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (haction : ∃ i : Nat, i < stop ∧
      rho.events[i]? = some (.tick a.val_index ta) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index ta)
    (hpair : a.height_pair.erase = HeightPair.target h root) :
    h ≠ blocked := by
  intro heq
  subst h
  obtain ⟨i, hiStop, hi, ho⟩ := haction
  exact WindowRecoveryInput.target_impossible S adm hcap hrec hiStop ha hi ho
    (stateBefore_target_none_recoveryHeight_named S adm hcap hrec ha i hiStop.le)
    (stateBefore_lock_none_recoveryHeight_named S adm hcap hrec ha i hiStop.le) hpair

/-- At the point schedule, the original pre-action cut suffices because the
paper-time input has no proposal duty (PROTOCOL.md `sec:healing-schedule`). -/
theorem honestEmittedTarget_height_ne_recovery_named_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {stop : Nat} {blocked hF0 h : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {a : NamedAttestation V} {ta : Time} {root : BlockId}
    (ha : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (haction : strictEventIndex rho (S.a a.round) ≤ stop)
    (hpair : a.height_pair.erase = HeightPair.target h root) :
    h ≠ blocked := by
  intro heq
  subst h
  have hrow : a.height_pair.erase.height? = some blocked := hpair ▸ rfl
  obtain ⟨D, _, _, haEq, hsource, _, hheight, _, _, -⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness_point S adm hpoint ha hemit hrow
  have htimeout := actionAttestationAt_height_pair_timeout_recoveryHeight_named
    S adm hcap hrec ha haction hsource hheight
  have herase := congrArg NamedHeightPair.erase htimeout
  rw [← haEq, hpair] at herase
  cases herase

#print axioms stateBefore_lock_none_recoveryHeight_named
#print axioms stateBefore_target_none_recoveryHeight_named
#print axioms actionAttestationAt_height_pair_timeout_recoveryHeight_named
#print axioms honestEmittedTarget_height_ne_recovery_named_point
#print axioms honestEmittedTarget_height_ne_recovery_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
