module
public import DecoupledConsensusProofs.Protocol.Grades.CommonSupportBase
public import DecoupledConsensusProofs.Protocol.Grades.SGFromSupport
public import DecoupledConsensusProofs.Protocol.Grades.WindowRoundHistory

/-!
# Causal outage round induction

The opening SG certificate uses the history before G0 completion. Only after
that certificate is established does the event induction extend through the
round's actions and supply the unchanged paper checkpoint
(PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Post-boundary emissions split into first-round stragglers and actual
included-round actions. Both floors are derived from opening frames and
causal FG histories, never an extra outage premise (PROTOCOL.md `sec:grades`). -/
theorem honest_confirmed_above_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : ∀ q, DomainIncluded S rho b0 q → q < r → RoundInvariant S rho b0 Pn q) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase := by
  apply hpost_of_first_round_and_included S rho b0 b1 s r0 r Pn hexec hmargin hsleep
    hscope hno hr0 hmin hfirst hframes hheld0
  intro a t hinc hlt ha hem hb
  have hq := hinv a.round hinc hlt
  exact NamedWindowSGFloor.confirmed_head_floor_of_opening S rho b0 b1 s Pn
    hexec hmargin hsleep hheld0 hq.entry_history ha hinc.1 hem hb (hq.sg a.val_index ha)

/-- Assemble one round only after earlier opening certificates have supplied
its causal pre-G0 history (PROTOCOL.md `sec:grades`). -/
private theorem roundInvariant_of_earlier
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase) (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0)
    (hr : DomainIncluded S rho b0 r)
    (hrb1 : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hall : ∀ q, DomainIncluded S rho b0 q → q < r → RoundInvariant S rho b0 Pn q) :
    RoundInvariant S rho b0 Pn r := by
  have hpost := honest_confirmed_above_of_invariant S rho b0 b1 s r0 r Pn hexec hmargin
    hsleep hscope hno hr0 hmin hfirst hconf.2.2 hheld0 hall
  have hentry : IntrinsicHighEntryHistoryIdx S rho Pn
      (strictEventCut rho (domain S.E S.hc r .g0)) := by
    by_cases heq : r = r0
    · subst r
      exact (NamedStragglerEntryHistory.first_round_event_history S rho b0 b1 s r0 Pn
        hexec hmargin hsleep hscope hno hmin hfirst hconf.2.2 hheld0 _ le_rfl).1
    · have hle : r0 ≤ r - 1 := Nat.le_pred_of_lt
        (lt_of_le_of_ne (hmin r hr.1 hr.2.1) (Ne.symm heq))
      have hpred : DomainIncluded S rho b0 (r - 1) :=
        ⟨lt_of_lt_of_le hr0.1 hle, hr0.2.1.trans (Assembly.a_mono S hle),
          (S.hc.domain_mono S.E .g1 (Nat.sub_le r 1)).trans hr.2.2⟩
      have hp := (hall (r - 1) hpred (Nat.sub_lt hr.1 (by decide))).entry_history
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr.1))] using hp
  have hband := NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band
    S rho b0 b1 s _ Pn hexec hmargin hsleep hentry
  have hgap : s + 1 < r := by
    by_contra hn
    have hm : S.a (s + 1) + S.E.Δ ≤ b0 := hmargin
    have hb := (hm.trans hr.2.1).trans (Assembly.a_mono S (Nat.not_lt.mp hn))
    exact absurd hb (not_le.mpr (lt_add_of_pos_right _ S.E.Δ_pos))
  have hsupport := common_support_base_at S rho b0 b1 v s r Pn hexec hsleep hforming hv
    hmargin hseed hscope hno hconf.1 hconf.2.1 hbudget hentry hr.1 hgap hrb1 hpost
  have hsg := sg_at_domain_read_of_common_support S rho b0 b1 s r Pn hexec hslash hsleep
    hforming hscope hr hmargin hno hband hentry hheld0 hpost
    ⟨hconf.1, hconf.2.1⟩ v hv hseed hsupport
  have hevents := NamedWindowRoundHistory.round_event_history S rho b0 b1 s r0 r Pn
    hexec hmargin hsleep hscope hno hr0 hmin hfirst hconf.2.2 hheld0
    (fun q hq hqr => by
      rcases lt_or_eq_of_le hqr with hlt | rfl
      · exact (hall q hq hlt).sg
      · exact hsg) _ le_rfl
  have hcheckpoint := NamedWindowRoundHistory.checkpoint_event_history S rho b0 b1 s r Pn
    hexec hmargin hsleep hevents.1
  exact {
    included := hr
    prefix_scope := hscope
    sg := hsg
    common_support := hsupport
    fg := fun _ w hw => by
      have h := fg_noninterference_after_boundary S rho b0 b1 s r Pn hexec hslash hmargin
        hsleep hscope hno hcheckpoint.2 hcheckpoint.1 hheld0 w hw (S.a r) hr.2.1 le_rfl
      exact ⟨h.2.1, h.2.2⟩
    source_history := NamedCheckpointRows.window_signed_source_history S rho
      hexec.core.toNamedScheduleWellFormed _
    old_rows := fun _ w _ B hB => NamedCheckpointRows.prior_carrier_rows_at_checkpoint S rho
      hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable w r hB
    entry_history := hevents.1
    conflicting_band := hevents.2 }

/-- The first included round uses the derived straggler floor and older-round
vacuity, with the original selection and outage boundary (PROTOCOL.md `sec:grades`). -/
theorem roundInvariant_base'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr : DomainIncluded S rho b0 r)
    (hrb1 : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hfirst : S.a (r - 1) < b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q) :
    RoundInvariant S rho b0 Pn r := by
  apply roundInvariant_of_earlier S rho b0 b1 v s r r Pn hexec hslash hsleep hforming
    hv hmargin hseed hscope hno hconf hbudget hheld0 hr hmin hfirst hr hrb1
  intro q hq hlt
  exact (Nat.not_lt_of_ge (hmin q hq.1 hq.2.1) hlt).elim

/-- All included round invariants with the corrected fold. -/
theorem roundInvariant_all_included'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr0 : DomainIncluded S rho b0 r0) (hfirst : S.a (r0 - 1) < b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (_hentry0 : IntrinsicHighEntryHistory S rho Pn r0) :
    ∀ r : Round, DomainIncluded S rho b0 r →
      domain S.E S.hc r .g2 ≤ b1 + S.E.Δ → RoundInvariant S rho b0 Pn r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hrb1
    apply roundInvariant_of_earlier S rho b0 b1 v s r0 r Pn hexec hslash hsleep hforming
      hv hmargin hseed hscope hno hconf hbudget hheld0 hr0 hmin hfirst hr hrb1
    intro q hq hlt
    exact ih q hlt hq ((base_domain_g2_mono S hlt.le).trans hrb1)

/-- Successor assembly uses the same support certificate producer, now with
the causal head floor for earlier included rounds (PROTOCOL.md `sec:grades`). -/
theorem roundInvariant_step'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase) (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0)
    (hall : ∀ q, DomainIncluded S rho b0 q → q ≤ r → RoundInvariant S rho b0 Pn q)
    (hnext : DomainIncluded S rho b0 (r + 1))
    (hrb1 : domain S.E S.hc (r + 1) .g2 ≤ b1 + S.E.Δ) :
    RoundInvariant S rho b0 Pn (r + 1) :=
  roundInvariant_of_earlier S rho b0 b1 v s r0 (r + 1) Pn hexec hslash hsleep hforming
    hv hmargin hseed hscope hno hconf hbudget hheld0 hr0 hmin hfirst hnext hrb1
    (fun q hq hlt => hall q hq (Nat.lt_succ_iff.mp hlt))

/-- Every field of the original checkpoint invariant is recovered at the
point instance, including strict histories at the original paper read
(PROTOCOL.md `sec:healing-schedule`). -/
theorem roundInvariant_point
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hpoint : ∀ v q, (S.node v).act q = S.a q)
    (hinv : RoundInvariant S rho b0 P r) : PointRoundInvariant S rho b0 P r := by
  have hh := NamedWindowRoundHistory.checkpoint_event_history_point S rho b0 b1 s r P
    hexec hmargin hsleep hinv.entry_history hpoint
  exact {
    included := hinv.included
    prefix_scope := hinv.prefix_scope
    sg := hinv.sg
    common_support := hinv.common_support
    fg := hinv.fg
    source_history := NamedCheckpointRows.signed_source_history S rho r
    old_rows := fun _ v _ B hB => NamedCheckpointRows.prior_carrier_rows_at_checkpoint_point
      S rho hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable hpoint v r hB
    entry_history := hh.1
    conflicting_band := hh.2 }

/-- The point instance recovers the original checkpoint conclusion,
including both strict histories (PROTOCOL.md `sec:healing-schedule`). -/
theorem roundInvariant_base_point'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr : DomainIncluded S rho b0 r)
    (hrb1 : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hfirst : S.a (r - 1) < b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hpoint : ∀ w q, (S.node w).act q = S.a q) :
    PointRoundInvariant S rho b0 Pn r :=
  roundInvariant_point S rho b0 b1 s r Pn hexec hmargin hsleep hpoint
    (roundInvariant_base' S rho b0 b1 v s r Pn hexec hslash hsleep hforming hv hmargin hseed hscope hno hconf hbudget hheld0 hr hrb1 hfirst hmin)

#print axioms roundInvariant_base_point'

/-- The point instance recovers the original checkpoint conclusion,
including both strict histories (PROTOCOL.md `sec:healing-schedule`). -/
theorem roundInvariant_step_point'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase) (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0)
    (hall : ∀ q, DomainIncluded S rho b0 q → q ≤ r → RoundInvariant S rho b0 Pn q)
    (hnext : DomainIncluded S rho b0 (r + 1))
    (hrb1 : domain S.E S.hc (r + 1) .g2 ≤ b1 + S.E.Δ)
    (hpoint : ∀ w q, (S.node w).act q = S.a q) :
    PointRoundInvariant S rho b0 Pn (r + 1) :=
  roundInvariant_point S rho b0 b1 s (r + 1) Pn hexec hmargin hsleep hpoint
    (roundInvariant_step' S rho b0 b1 v s r0 r Pn hexec hslash hsleep hforming hv hmargin hseed hscope hno hconf hbudget hheld0 hr0 hmin hfirst hall hnext hrb1)

#print axioms roundInvariant_step_point'

#print axioms honest_confirmed_above_of_invariant
#print axioms roundInvariant_base'
#print axioms roundInvariant_step'
#print axioms roundInvariant_all_included'
#print axioms roundInvariant_point
end DecoupledConsensusModel.Proofs.NamedOutageClosure
