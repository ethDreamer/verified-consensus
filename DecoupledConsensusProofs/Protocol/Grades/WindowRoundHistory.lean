module
public import DecoupledConsensusProofs.Protocol.Grades.WindowRoundBase

/-!
# Causal history through included rounds

Opening SG certificates extend the straggler event induction through the
current round. The resulting history includes early current-round emissions
at the unchanged paper checkpoint and late actions after that checkpoint
(PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowRoundHistory
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open Internal.NamedOutageEntry NamedOutageClosure
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Opening certificates for included rounds, together with the pre-boundary
frames for stragglers, close both causal history arms up to the next G0
completion. The opening certificates are induction conclusions, not a new
execution assumption (PROTOCOL.md `sec:grades`). -/
theorem round_event_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (hsg : ∀ q, DomainIncluded S rho b0 q → q ≤ r → ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc q .g1) v
      Block.Preceq P.erase n.st.core.F ∨
        ∃ raw, (readFrame n.cache n.st.core.toHealing q).g2 = some (some raw) ∧
          Block.Preceq P.erase raw) :
    ∀ n, n ≤ strictEventCut rho (domain S.E S.hc (r + 1) .g0) →
      IntrinsicHighEntryHistoryIdx S rho P n ∧ IntrinsicConflictingCarrierBandIdx S rho P n := by
  have hall : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi a source entry ha hs
      by_cases hb : (S.node a.val_index).act a.round < b0
      · exact NamedWindowIntrinsicEntry.signed_entry_pre_boundary S rho b0 P hP hno ha hs hb
      · have hh : IntrinsicHighEntryHistoryIdx S rho P i := by
          intro j hj a' source' entry' ha' hs'
          exact ih j hj (hj.trans hi) a' source' entry' ha' hs'
        have ht := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted
          (domain S.E S.hc (r + 1) .g0) hi hs.1
        have har : a.round ≤ r :=
          Nat.lt_succ_iff.mp (S.round_lt_of_act_lt_domain a.val_index ht)
        apply NamedStragglerEntryHistory.entry_compatible_of_opening S rho b0 b1 s P
          hexec hmargin hsleep hP hheld0 hh ha hs (le_of_not_gt hb)
        by_cases hprior : a.round < r0
        · exact straggler_opening_frame S rho b0 s r0 P hmargin hmin hfirst hframes ha
            ⟨i, hs.1, hs.2.1⟩ (le_of_not_gt hb) hprior
        · have hge := Nat.le_of_not_gt hprior
          have hhor := (hexec.core.in_horizon _ (List.mem_iff_getElem?.mpr ⟨i, hs.1⟩)).2
          have hopen : domain S.E S.hc a.round .g1 ≤ (S.node a.val_index).act a.round := by
            simpa only [domain, Phase.domainOffset, zero_mul, add_zero] using
              S.opening_le_act a.val_index a.round
          exact hsg a.round ⟨lt_of_lt_of_le hr0.1 hge,
            hr0.2.1.trans (Assembly.a_mono S hge), hopen.trans hhor⟩ har a.val_index ha
  intro n hn
  have hh : IntrinsicHighEntryHistoryIdx S rho P n := by
    intro i hi a source entry ha hs
    exact hall i (lt_of_lt_of_le hi hn) a source entry ha hs
  exact ⟨hh, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band
    S rho b0 b1 s n P hexec hmargin hsleep hh⟩

/-- A completed opening certificate extends the history before this round's
G0 completion through all of its action events. Earlier-round actions already
belong to the input history by P2 (PROTOCOL.md `sec:healing-schedule`). -/
theorem extend_round_event_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (hbefore : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc r .g0)))
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq P.erase n.st.core.F ∨
        ∃ raw, (readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
          Block.Preceq P.erase raw) :
    IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi a source entry ha hs
    by_cases hold : i < strictEventCut rho (domain S.E S.hc r .g0)
    · exact hbefore i hold a source entry ha hs
    · by_cases hb : (S.node a.val_index).act a.round < b0
      · exact NamedWindowIntrinsicEntry.signed_entry_pre_boundary S rho b0 P hP hno ha hs hb
      · have hh : IntrinsicHighEntryHistoryIdx S rho P i := by
          intro j hj a' source' entry' ha' hs'
          exact ih j hj (hj.trans hi) a' source' entry' ha' hs'
        have ht := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted
          (domain S.E S.hc (r + 1) .g0) hi hs.1
        have har : a.round ≤ r :=
          Nat.lt_succ_iff.mp (S.round_lt_of_act_lt_domain a.val_index ht)
        have heq : a.round = r := by
          by_contra hne
          have hlt : a.round < r := lt_of_le_of_ne har hne
          exact hold (NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
            (domain S.E S.hc r .g0) hs.1
            (NamedStragglerEntryHistory.action_before_completion_of_round_lt S a.val_index hlt))
        apply NamedStragglerEntryHistory.entry_compatible_of_opening S rho b0 b1 s P
          hexec hmargin hsleep hP hheld0 hh ha hs (le_of_not_gt hb)
        simpa only [heq] using hsg a.val_index ha

/-- Restrict the causal producer to the original paper checkpoint. P1 permits
current-round emissions in this strict prefix, and they are included here
(PROTOCOL.md `sec:healing-schedule`). -/
theorem checkpoint_event_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hhistory : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0))) :
    IntrinsicHighEntryHistoryIdx S rho P (strictEventCut rho (S.a r)) ∧
      IntrinsicConflictingCarrierBandIdx S rho P (strictEventCut rho (S.a r)) := by
  have hcut : S.a r < domain S.E S.hc (r + 1) .g0 := by
    have hend := S.hc.a_before_round_end S.E r
    have hd := S.E.Δ_pos
    change S.hc.a S.E.Δ r < _
    simp only [domain, Phase.domainOffset]
    linarith
  have hh : IntrinsicHighEntryHistoryIdx S rho P (strictEventCut rho (S.a r)) := by
    intro i hi a source entry ha hs
    have ht := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted
      (S.a r) hi hs.1
    exact hhistory i (NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
      (domain S.E S.hc (r + 1) .g0) hs.1 (lt_trans ht hcut)) a source entry ha hs
  exact ⟨hh, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band
    S rho b0 b1 s _ P hexec hmargin hsleep hh⟩

/-- The original two paper-checkpoint producers follow at the point instance,
with their strict prior-round scope unchanged (PROTOCOL.md `sec:healing-schedule`). -/
theorem checkpoint_event_history_point
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hhistory : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0)))
    (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    IntrinsicHighEntryHistory S rho P r ∧ IntrinsicConflictingCarrierBand S rho P r := by
  have hh := (checkpoint_event_history S rho b0 b1 s r P hexec hmargin hsleep hhistory).1
  have hp := (NamedWindowIntrinsicEntry.intrinsic_history_point_iff S rho
    hexec.core.toNamedScheduleWellFormed hpoint P r).1 hh
  exact ⟨hp, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band_point
    S rho b0 b1 s r P hexec hmargin hsleep hpoint hp⟩

#print axioms extend_round_event_history
#print axioms round_event_history
#print axioms checkpoint_event_history
#print axioms checkpoint_event_history_point
end DecoupledConsensusModel.Proofs.NamedWindowRoundHistory
