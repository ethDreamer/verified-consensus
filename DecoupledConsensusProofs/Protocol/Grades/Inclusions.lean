module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference

@[expose] public section

/-!
# The two set inclusions behind the base common-support weight bound (L6b)

`GradeFormingMajority` at the support round `sr` reads

  `weightOf ((univ \ honest) ∪ staleHistoricalVoters sr) < weightOf (honestRoundVoters (sr-1))`,

and the `common_support` field needs the same inequality with
`commonStaleRisks … sr r` on the left and `commonSupporters … sr r` on the
right. The two theorems here are exactly that transfer. Ready post-boundary
rows use the derived `hpost` head floor. They are stated for an
arbitrary support round `sr` with `s + 1 ≤ sr` and `opening sr ≤ b0`; the
boundary round of `CommonSupportBase.lean` supplies both.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Copied from the `local instance` of `NamedJointOutage`. -/
local instance decidableNeedsSGInclusions (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (r : Round) (v : V) :
    Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))


/-! ## Window arithmetic

These four declarations were in `CommonSupportBase.lean`; they move here
unchanged so that both inclusions and the base certificate can use them. -/


/-- Arithmetic over bare `Int`: an integer strictly below `y + 1` is at most
`y`. Stated here because `omega` will not read a `Time`-stated hypothesis. -/
private theorem le_of_lt_succ_int : ∀ x y : Int, x < y + 1 → x ≤ y := by
  intro x y h; omega

/-- The round opening is strictly before the round action: the G1 domain offset
is zero and the action is `6Δ` past the opening. This is what replaces the
boundary lower bound `b0 ≤ S.a r` in `voters_subset_supporters_at`. -/
private theorem opening_lt_action (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 < S.a r := by
  have he : S.a r = domain S.E S.hc r .g1 + 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact lt_add_of_pos_right _ (Int.mul_pos (by decide : (0 : Int) < 6) S.E.Δ_pos)


private theorem window_witness : ∀ eta r k : Nat, r - eta ≤ k → k < r →
    k - (r - eta) < min r eta ∧ k = r - eta + (k - (r - eta)) := by
  intro eta r k h1 h2
  exact ⟨by omega, by omega⟩

/-- `r − η ≤ k < r` puts `k` in `latest_window η r`. -/
theorem mem_latest_window {eta r k : Round} (hlo : r - eta ≤ k) (hhi : k < r) :
    k ∈ Protocol.latest_window eta r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul]
  exact ⟨k - (r - eta), (window_witness eta r k hlo hhi).1,
    (window_witness eta r k hlo hhi).2⟩

/-- Copied from the private helper of the same name in `NamedOutageInputs`. -/
theorem window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega



/-! ## Small `Nat` helpers (the toolchain note: `omega` at bare `Nat`) -/

private theorem sub_eta_le_pred : ∀ n e : Nat, 1 ≤ e → n - e ≤ n - 1 := by
  intro n e h; omega

private theorem pred_succ_of_pos : ∀ s n : Nat, s + 1 ≤ n → n - 1 + 1 = n := by
  intro s n h; omega

private theorem le_pred_of_succ_le : ∀ s n : Nat, s + 1 ≤ n → s ≤ n - 1 := by
  intro s n h; omega


private theorem succ_lt_of_lt_of_succ_le :
    ∀ s n x : Nat, s + 1 ≤ n → x < s → x + 1 < n := by
  intro s n x h1 h2; omega

private theorem absurd_low : ∀ s n x : Nat, s + 1 ≤ n → n - 1 ≤ x → x < s → False := by
  intro s n x h1 h2 h3; omega

private theorem le_pred_of_lt : ∀ q r : Nat, q < r → q ≤ r - 1 := by
  intro q r h; omega



/-- `readAt` is the strict read one instant later. -/
theorem incl_readAt_eq_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hp : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e : NamedEvent V => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hp]

/-- Time-monotone growth of the finalized prefix at a named strict read, over
the index bridge of `RowTrace`. -/
theorem incl_strict_F_mono (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (NamedRun.stateBeforeTime S rho c reader).st.core.F
      (NamedRun.stateBeforeTime S rho d reader).st.core.F := by
  rw [strict_read_eq_index S rho sch.sorted c, strict_read_eq_index S rho sch.sorted d]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho reader (strict_lengths_mono rho hcd)

/-- The G1 domain IS the round opening: its domain offset is zero. -/
theorem incl_domain_g1_eq_opening (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 = opening S.E S.hc r := by
  simp only [domain, Phase.domainOffset]
  ring

/-- The round-`r` G2 domain is inside the round-`r` opening read. -/
theorem incl_g2_le_opening_cut (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 ≤ domain S.E S.hc r .g1 + 1 := by
  rw [incl_domain_g1_eq_opening]
  exact Int.le_add_one (domain_le_opening S r)

/-- The opening precedes the action by `6Δ`. -/
theorem incl_opening_le_a (S : Setup V) (r : Round) : opening S.E S.hc r ≤ S.a r := by
  have h : S.a r = opening S.E S.hc r + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, opening, Protocol.proposal_time, Env.t, slotStart]
  rw [h]
  simpa only [add_zero] using
    Int.add_le_add_left (Int.mul_nonneg (by decide) S.E.Δ_pos.le) (opening S.E S.hc r)

/-- **The guard, from `NeedsSG` and a finality row.** The caller supplies the
comparison of the protected prefix with the reader's finalized block at the read
in question; `NeedsSG` rules out the `P ⪯ F` side. -/
theorem finalized_le_of_needsSG (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (r : Round) (Pn : NamedBlock V)
    (w : V) (hneed : NeedsSG S rho Pn r w) (cut : Time)
    (hcut : cut ≤ domain S.E S.hc r .g1 + 1)
    (hcompat : Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho cut w).st.core.F = true) :
    Block.Preceq (NamedRun.stateBeforeTime S rho cut w).st.core.F Pn.erase := by
  rcases (show Block.Preceq Pn.erase (NamedRun.stateBeforeTime S rho cut w).st.core.F ∨
      Block.Preceq (NamedRun.stateBeforeTime S rho cut w).st.core.F Pn.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using! hcompat) with hPle | hFle
  · exfalso
    refine hneed ?_
    have hstage : NamedRun.readAt S rho (domain S.E S.hc r .g1) w =
        NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) w := by
      rw [incl_readAt_eq_succ]
    rw [hstage]
    exact Block.preceq_trans hPle (incl_strict_F_mono S rho sch w hcut)
  · exact hFle

/-- The guard at a read at or before the boundary, from the clean-tier finality
row `NamedFinalityGuard.finalized_representative_compatible_before_boundary`.
No entry-history premise is needed at such a read. -/
theorem finalized_le_before_boundary (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (w : V) (hw : w ∈ rho.honest) (hneed : NeedsSG S rho Pn r w)
    (cut : Time) (hcut : cut ≤ b0) (hcutr : cut ≤ domain S.E S.hc r .g1 + 1) :
    Block.Preceq (NamedRun.stateBeforeTime S rho cut w).st.core.F Pn.erase := by
  obtain ⟨F, _, hFe, hFcompat⟩ :=
    NamedFinalityGuard.finalized_representative_compatible_before_boundary S rho b0 b1 s
      hexec hmargin hsleep Pn hPn hno w hw cut hcut
  exact finalized_le_of_needsSG S rho hexec.core.toNamedScheduleWellFormed r Pn w hneed cut
    hcutr (by rw [← hFe]; exact Proofs.NamedWire.erase_compatible hFcompat)

/-- The guard at the round-`r` G2 domain read, which can be past the boundary.
This is the tier that needs `IntrinsicHighEntryHistory`. -/
theorem finalized_le_at_g2_domain (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn (strictEventCut rho (domain S.E S.hc r .g0)))
    (w : V) (hw : w ∈ rho.honest) (hneed : NeedsSG S rho Pn r w) :
    Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F Pn.erase :=
  finalized_le_of_needsSG S rho hexec.core.toNamedScheduleWellFormed r Pn w hneed
    (domain S.E S.hc r .g2) (incl_g2_le_opening_cut S r)
    (finalized_compatible_after_boundary S rho b0 b1 s r Pn hexec hmargin hsleep hentry w hw
      (domain S.E S.hc r .g2) ((incl_g2_le_opening_cut S r).trans (S.opening_read_le_completion r)))

/-! ## The stale inclusion -/

/-- The stale inclusion at a general inventory time `tau ≤ b0`. Only the
inventory read moves; healthy delivery and the two stage-1 premises are still
stated at `b0` and apply a fortiori, because every retained row at `tau` has
its action strictly before `tau ≤ b0`. -/
theorem stale_risks_subset_at (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (b0 b1 tau : Time) (htau : tau ≤ b0) (hgrid : OnDeltaGrid S tau)
    (s sr r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hcutr : tau ≤ domain S.E S.hc r .g1 + 1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hlo : s + 1 ≤ sr) (hopen : opening S.E S.hc sr ≤ tau) :
    commonStaleRisks S rho tau Pn sr r ⊆ staleHistoricalVoters S rho sr := by
  intro u hu
  obtain ⟨huh, w, hw, hneeds, hstale⟩ := Finset.mem_filter.mp hu
  have hFP : Block.Preceq (NamedRun.stateBeforeTime S rho tau w).st.core.F Pn.erase :=
    finalized_le_before_boundary S rho b0 b1 s r Pn hexec hmargin hsleep hPn hno w hw hneeds
      tau htau hcutr
  obtain ⟨x, hx, hxs⟩ := exists_low_round_of_staleAt_at S rho sch auth roots b0 tau htau hgrid s
    Pn.erase hconf hhead w hw u huh hFP sr hstale
  obtain ⟨a, hval, haround, _hproj, hrounds, _hlt, hem⟩ :=
    retained_trace S rho sch auth tau w sr u huh (latest_mem hx).1
  have hvote : u ∈ honestRoundVoters S rho x.round :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u x.round).mpr
      ⟨huh, a, hval, haround, by simpa only [haround, hval] using hem⟩
  have hqmem : sr - 1 ∈ Internal.OutageEntryRevision.retainedRounds S sr :=
    mem_retainedRounds S (sub_eta_le_pred sr S.hc.η_SG S.hc.η_SG_ge_one) (Nat.sub_le sr 1)
  have hopen' : opening S.E S.hc (sr - 1 + 1) ≤ tau := by
    rw [pred_succ_of_pos s sr hlo]; exact hopen
  have hnot : u ∉ honestRoundVoters S rho (sr - 1) := by
    intro hvote1
    obtain ⟨c, _hcval, hcround, _hcem, _hcdead, hcmem⟩ :=
      retained_mem_of_vote_at S rho sch harr hR sr (sr - 1) u hvote1 hqmem tau htau hopen' w hw
    have hle : c.round ≤ x.round := latest_ge_of_mem hx hcmem
    exact absurd_low s sr x.round hlo (hcround ▸ hle) hxs
  refine Finset.mem_sdiff.mpr ⟨?_, hnot⟩
  exact Proofs.NamedOutageInputs.historical_of_vote S rho (retainedRounds_bounds S hrounds).1
    (succ_lt_of_lt_of_succ_le s sr x.round hlo hxs) hvote

theorem stale_risks_subset (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (b0 b1 : Time) (s sr r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hcutr : b0 ≤ domain S.E S.hc r .g1 + 1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hlo : s + 1 ≤ sr) (hopen : opening S.E S.hc sr ≤ b0) :
    commonStaleRisks S rho b0 Pn sr r ⊆ staleHistoricalVoters S rho sr :=
  stale_risks_subset_at S rho sch auth roots hR b0 b1 b0 le_rfl
    (onDeltaGrid_of_public S b0 hexec.boundaryPublic) s sr r Pn hexec hmargin hsleep hPn hno
    hcutr hconf hhead harr hlo hopen

/-! ## Coverage of a raw phase input at the round-`r` G2 read -/

/-- Every raw input of an honest sender in round `r`'s G2 window, from a round
at or above the stable round, covers the protected prefix at an honest
reader's round-`r` G2 store. The row's round is below `r`, so its action is at
or before `S.a (r - 1) < b0` and both stage-1 premises apply. -/
theorem rawInputs_localCovers (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (b0 : Time) (s r : Round) (Pn : NamedBlock V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase) (hfirst : ∀ v, (S.node v).act (r - 1) < b0)
    (hpub : Execution.PublicTime S b0)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F Pn.erase)
    (u : V) (hu : u ∈ rho.honest) (cutoff : Time)
    {z : Protocol.SGVote V}
    (hz : z ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      S.hc.η_SG r cutoff u)
    (hzs : s ≤ z.round) :
    localCovers
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      z.confirmed Pn.erase = true := by
  obtain ⟨b, hbval, hbround, hbproj, hbwin, _hblt, hbem⟩ :=
    rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) cutoff w S.hc.η_SG r u hu hz
  have hzr : z.round < r := (window_bounds hbwin).2
  have hbr : b.round < r := by rw [hbround]; exact hzr
  have hlt : (S.node b.val_index).act b.round < b0 :=
    lt_of_le_of_lt (by
      rcases Nat.eq_or_lt_of_le (le_pred_of_lt b.round r hbr) with he | hl
      · rw [he]
      · exact ((S.act_before_round_end b.val_index b.round).trans_le
          ((opening_mono S hl).trans (S.opening_le_act b.val_index (r - 1)))).le)
      (hfirst b.val_index)
  have hbs : s ≤ b.round := by rw [hbround]; exact hzs
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hbem
  have hdelta : (S.node b.val_index).act b.round + S.E.Δ ≤ b0 := act_add_delta_le_of_lt_grid S b0 (onDeltaGrid_of_public S b0 hpub) b.val_index b.round hlt
  obtain ⟨H, hH, hroot, _, _⟩ :=
    hhead b ((S.node b.val_index).act b.round) (hbval ▸ hu) (hbval ▸ hbem) hdelta hbs w hw (domain S.E S.hc r .g2)
      ((S.act_deadline_le_early b.val_index hbr).trans (early_le_domain S r)) hFP K.root hkey
  have hHrun : NamedRun.blockInRun S rho H :=
    held_blockInRun S rho sch w hw (domain S.E S.hc r .g2) hH
  have hcover : Block.Preceq Pn.erase H.erase :=
    hconf b ((S.node b.val_index).act b.round) (hbval ▸ hu) (hbval ▸ hbem) hlt hbs K.root hkey H hHrun hroot
  have hfind : Block.find? (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T
      H.root = some H.erase := by
    simpa only [Proofs.NamedWire.erase_root] using
      held_find_at_strict S rho sch roots w hw (domain S.E S.hc r .g2) H hH
  have hzconf : z.confirmed = some H.root := by rw [← hbproj, sgVote_confirmed, hkey, hroot]
  change Protocol.head_covers _ Pn.erase z.confirmed = true
  rw [hzconf]
  show (match Block.find? (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T
      H.root with
    | some head => Block.preceq Pn.erase head
    | none => false) = true
  rw [hfind]
  exact hcover

/-- A root that resolves at an honest reader's strict read resolves to a
retained body, hence to a run block. This is the converse of
`NamedHealthyHeadReady.held_find_at_strict`, and it is what lets the
post-boundary premise, which speaks of run blocks, be applied to the reader's
own lookup. -/
private theorem incl_find_body_at_strict (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) (hreader : reader ∈ rho.honest)
    (t : Time) {key : BlockId} {Hb : Block V}
    (hfind : Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T key = some Hb) :
    ∃ H : NamedBlock V, NamedRun.blockInRun S rho H ∧ H.erase = Hb ∧ H.root = key := by
  obtain ⟨m, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hfind
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho m reader).1.1.1
  have hmem : Hb ∈ (NamedRun.stateBefore S rho m reader).st.core.T :=
    Proofs.HealingLemmas.find?_mem hfind
  rw [hcoh.1] at hmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hmem
  refine ⟨H, Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader m hH), hHe, ?_⟩
  rw [← Proofs.NamedWire.erase_root H, hHe]
  exact Proofs.HealingLemmas.find?_root hfind

/-- Every body-ready input of an honest sender in round `r`'s window covers the
protected prefix at an honest reader's round-`r` G2 store. The sender's row is
either a pre-boundary emission (`hconf`) or a post-boundary emission of a round
below `r` (`hpost`), and the reader's own resolution of the confirmed root
comes from `bodyReady` itself, so `HonestHeadHeldAbove` is not consulted. This
is the `hfirst`-free replacement for `Inclusions.rawInputs_localCovers`. -/
theorem interpreted_localCovers (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (b0 : Time) (s r : Round) (Pn : NamedBlock V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (w : V) (hw : w ∈ rho.honest) (u : V) (hu : u ∈ rho.honest) (cutoff : Time)
    {z : Protocol.SGVote V}
    (hz : z ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r cutoff u)
    (hzs : s ≤ z.round) :
    localCovers
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      z.confirmed Pn.erase = true := by
  obtain ⟨hzraw, hready⟩ := Finset.mem_filter.mp hz
  obtain ⟨b, hbval, hbround, hbproj, hbwin, _hblt, hbem⟩ :=
    rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) cutoff w S.hc.η_SG r u hu hzraw
  have hzr : z.round < r := (window_bounds hbwin).2
  have hbr : b.round < r := by rw [hbround]; exact hzr
  have hbs : s ≤ b.round := by rw [hbround]; exact hzs
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hbem
  have hzconf : z.confirmed = some K.root := by rw [← hbproj, sgVote_confirmed, hkey]
  have hfindsome : ∃ Hb : Block V,
      Block.find? (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root
        = some Hb := by
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some Hb => exact ⟨Hb, rfl⟩
    | none =>
      exfalso
      have hfalse : DecoupledConsensusModel.Protocol.bodyReady
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F cutoff z
            = false := by
        simp only [DecoupledConsensusModel.Protocol.bodyReady, Protocol.HealingStore.gradeView,
          Protocol.Store.toHealing, hzconf, hf]
      rw [hfalse] at hready
      exact absurd hready (by simp)
  obtain ⟨Hb, hfind⟩ := hfindsome
  obtain ⟨H, hHrun, hHe, hHroot⟩ :=
    incl_find_body_at_strict S rho sch w hw (domain S.E S.hc r .g2) hfind
  have hcover : Block.Preceq Pn.erase H.erase := by
    by_cases hlt : (S.node b.val_index).act b.round < b0
    · exact hconf b ((S.node b.val_index).act b.round) (hbval ▸ hu) (hbval ▸ hbem) hlt hbs K.root hkey H hHrun
        hHroot
    · exact hpost b ((S.node b.val_index).act b.round) (hbval ▸ hu) (hbval ▸ hbem) (not_lt.mp hlt) hbr
        K.root hkey H hHrun hHroot
  change Protocol.head_covers
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T Pn.erase z.confirmed
      = true
  rw [hzconf]
  show (match Block.find?
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some head => Block.preceq Pn.erase head
    | none => false) = true
  rw [hfind, ← hHe]
  exact hcover

/-! ## The supporter inclusion -/

/-- Every honest voter of the round below the support round is a common
supporter at the support boundary. Clause 1 is the healthy arrival of that
voter's own row plus `HonestHeadHeldAbove`; clauses 2 and 3 read off
`retained_covers`; clause 4 is the round-`r` G2 support predicate, where
`hfirst` makes every honest row in the round-`r` window a pre-outage emission
so that the two stage-1 premises still apply.

This is the general form at an inventory time `tau ≤ b0`. Clauses 1-3 are read
at `tau`; clause 4 is the round-`r` G2 phase read and does not move. -/
theorem voters_subset_supporters_at (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (b0 b1 tau : Time) (htau : tau ≤ b0) (hgrid : OnDeltaGrid S tau)
    (s sr r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn (strictEventCut rho (domain S.E S.hc r .g0)))
    (hcutr : tau ≤ domain S.E S.hc r .g1 + 1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hlo : s + 1 ≤ sr) (hopen : opening S.E S.hc sr ≤ tau)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (hwindow : sr - 1 ∈ Protocol.latest_window S.hc.η_SG r) :
    honestRoundVoters S rho (sr - 1) ⊆ commonSupporters S rho tau Pn sr r := by
  intro u hu
  have huh : u ∈ rho.honest := (Finset.mem_filter.mp hu).1
  refine Finset.mem_filter.mpr ⟨huh, ?_⟩
  intro w hw hneeds
  have hFPtau : Block.Preceq (NamedRun.stateBeforeTime S rho tau w).st.core.F Pn.erase :=
    finalized_le_before_boundary S rho b0 b1 s r Pn hexec hmargin hsleep hPn hno w hw hneeds
      tau htau hcutr
  have hFPdom : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F Pn.erase :=
    finalized_le_at_g2_domain S rho b0 b1 s r Pn hexec hmargin hsleep hentry w hw hneeds
  have hqmem : sr - 1 ∈ Internal.OutageEntryRevision.retainedRounds S sr :=
    mem_retainedRounds S (sub_eta_le_pred sr S.hc.η_SG S.hc.η_SG_ge_one) (Nat.sub_le sr 1)
  have hopen' : opening S.E S.hc (sr - 1 + 1) ≤ tau := by
    rw [pred_succ_of_pos s sr hlo]; exact hopen
  have hspred : s ≤ sr - 1 := le_pred_of_succ_le s sr hlo
  have hsrlt : sr - 1 < r := (window_bounds hwindow).2
  obtain ⟨a, hval, haround, hem, hdead, hraw⟩ :=
    retained_mem_of_vote_at S rho sch harr hR sr (sr - 1) u hu hqmem tau htau hopen' w hw
  have hsa : s ≤ a.round := by rw [haround]; exact hspred
  have hready : Protocol.sgVote a.erase ∈
      Internal.OutageEntryRevision.retainedReady S
        (NamedRun.stateBeforeTime S rho tau w).st.core sr tau u :=
    Finset.mem_filter.mpr ⟨hraw,
      retained_bodyReady S rho sch roots b0 s Pn.erase hhead w hw u huh hval hsa
        (hdead.trans htau) hem tau tau hdead hFPtau hdead⟩
  refine ⟨latest_nonempty ⟨_, hready⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hyraw : y ∈ Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho tau w).st.core sr tau u :=
      (Finset.mem_filter.mp (latest_mem hy).1).1
    have hyge : a.round ≤ y.round := (latest_mem hy).2 _ hready
    have hys : s ≤ y.round := le_trans hsa hyge
    refine ⟨retained_covers_at S rho sch auth roots b0 tau htau hgrid s Pn.erase hconf hhead w hw
      u huh hFPtau sr hyraw hys, ?_⟩
    obtain ⟨c, _, hcround, _, _, hclt, _⟩ := retained_trace S rho sch auth tau w sr u huh hyraw
    -- The emission `c` behind a retained row acted strictly before the
    -- inventory time, which is inside the round-`r` opening read; the opening is
    -- strictly before the round-`r` action, so `c` acted strictly before it.
    -- This is what the boundary bound `b0 ≤ S.a r` supplies, and it is
    -- available on both sides of the boundary.
    have hylt : y.round < r := by
      rw [← hcround]
      exact S.round_lt_of_act_lt_domain c.val_index
        (hclt.trans_le (hcutr.trans (S.opening_read_le_completion r)))
    exact mem_latest_window (le_trans (window_bounds hwindow).1 (haround ▸ hyge)) hylt
  · refine staleAt_false_of_rounds_ge_at S rho sch auth roots b0 tau htau hgrid s Pn.erase hconf
      hhead w hw u huh hFPtau sr ?_
    intro z hz
    exact le_trans hsa ((latest_mem hz).2 _ hraw)
  · obtain ⟨c, hcval, hcround, hcem, hcdead, hcraw⟩ :=
      rawInputs_mem_of_vote S rho sch harr hR (sr - 1) r u hu hwindow hsrlt
        (hopen'.trans htau) w hw
    have hcs : s ≤ c.round := by rw [hcround]; exact hspred
    have hcrlt : c.round < r := by rw [hcround]; exact hsrlt
    have hcready := retained_bodyReady S rho sch roots b0 s Pn.erase hhead w hw u huh hcval hcs
      hcdead hcem (domain S.E S.hc r .g2) (early S.E S.hc r .g2)
      ((S.act_deadline_le_early c.val_index hcrlt).trans (early_le_domain S r)) hFPdom
      (S.act_deadline_le_early c.val_index hcrlt)
    have hcinterp : Protocol.sgVote c.erase ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) u :=
      Finset.mem_filter.mpr ⟨hcraw, hcready⟩
    obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image
      (DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) u)
      (fun z : Protocol.SGVote V => z.round) ⟨_, hcinterp⟩
    have hyraw : y ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g2) u := (Finset.mem_filter.mp hy).1
    have hys : s ≤ y.round := le_trans hcs (hymax _ hcinterp)
    refine decide_eq_true ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy,
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
      exact hymax _ hz'
    · exact interpreted_localCovers S rho sch auth b0 s r Pn hconf hpost
        w hw u huh (early S.E S.hc r .g2) hy hys
    · intro tx htx ty hty _ hround
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp htx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hty
      obtain ⟨p, _, hpround, hpproj, _, _, hpem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) w
          S.hc.η_SG r u huh hx'
      obtain ⟨q, _, hqround, hqproj, _, _, hqem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) w
          S.hc.η_SG r u huh hy'
      have hpq : p = q := NamedOutageProvenance.emitted_same_round_unique S rho sch hpem hqem
        (by rw [hpround, hqround]; exact hround)
      show x'.confirmed = y'.confirmed
      rw [← hpproj, ← hqproj, hpq]
    · intro tz htz hltz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp htz
      have hzraw : z' ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG r (late S.E S.hc r .g2) u := (Finset.mem_filter.mp hz').1
      exact interpreted_localCovers S rho sch auth b0 s r Pn hconf hpost
        w hw u huh (late S.E S.hc r .g2) hz'
        (le_of_lt (lt_of_le_of_lt hys hltz))


#print axioms stale_risks_subset_at
#print axioms voters_subset_supporters_at
#print axioms stale_risks_subset
#print axioms rawInputs_localCovers

/-! ## The formation `kMin` bound

`predecessor_round_in_window` carries `hk: k ≤ s` as a hypothesis because
reading `u.round` off bucket membership was not available. `own_strict_read`
now supplies it, so the bound is proved here. The formation read only calls
`Protocol.NamedStore.setClock`, which leaves the row pool and the bucketed
projection untouched, so the traceback of `RowTrace.lean` applies verbatim. -/


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
