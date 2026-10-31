module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint

@[expose] public section

/-!
# Index-bounded joint history

Emission clauses read actual action inputs and range over tick indices
strictly before the boundary. Finalized prefixes range through the boundary.
The point-recovery lemmas specialize every emission field to the paper clock.
Confirmation and witness provenance name actual action inputs
(PROTOCOL.md `sec:healing-schedule`).
-/


namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The emission clauses parameterized by their input observer and action
clock (PROTOCOL.md `sec:healing-schedule`). -/
def LayerAHistoryIdxUsing (S : Setup V) (rho : NamedRun V)
    (read : V → NamedNodeState V → Round → NamedNodeState V)
    (act : V → Round → Time) (n : Nat)
    (C : NamedBlock V) : Prop :=
  NamedRun.blockInRun S rho C ∧
    (∀ (i : Nat) (v : V) (ta : Time) (a : NamedAttestation V),
      v ∈ rho.honest → rho.events[i]? = some (.tick v ta) →
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v ta → i < n →
      ∀ fp : FinalityPair, a.finality_pair = some fp →
        let n := read v (NamedRun.stateBefore S rho i v) a.round
        let gc := NamedProfile.gradeContract n.cache
        let input := Protocol.NamedActions.creatorInput
          (Protocol.attestation_input_with gc S.E S.hc (S.node v) n.st.core.toHealing)
        let st := n.st.core.toHealing
        let head := Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
          ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s
        ∃ H K : NamedBlock V,
          NamedRun.blockInRun S rho H ∧ H ∈ n.st.bodies ∧ H.erase = head ∧
          NamedRun.blockInRun S rho K ∧ K ∈ n.st.bodies ∧
          K.erase = (n.st.core.σ H.erase).J ∧
          a.val_index = v ∧ ta = act v a.round ∧
          a = (Protocol.NamedRecord.create n.record input).2 ∧
          fp.height = input.h_j ∧ fp.target = input.J ∧
          input.h_j = (n.st.core.σ H.erase).h_j ∧
          input.J = (n.st.core.σ H.erase).J.root ∧
          input.h_F = (n.st.core.σ H.erase).h_F ∧
          fp.target = K.root ∧ NamedBlock.Preceq K C) ∧
    (∀ (i : Nat) (v : V) (ta : Time) (a : NamedAttestation V),
      v ∈ rho.honest → rho.events[i]? = some (.tick v ta) →
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v ta → i < n →
      ∀ (h : Height) (T : BlockId) (timeout : Bool),
        a.height_pair = .vote h T timeout →
        let n := read v (NamedRun.stateBefore S rho i v) a.round
        let gc := NamedProfile.gradeContract n.cache
        let input := Protocol.NamedActions.creatorInput
          (Protocol.attestation_input_with gc S.E S.hc (S.node v) n.st.core.toHealing)
        ∃ source entry : NamedBlock V,
          NamedRun.blockInRun S rho source ∧ source ∈ n.st.bodies ∧
          NamedRun.blockInRun S rho entry ∧ entry ∈ n.st.bodies ∧
          a.val_index = v ∧ ta = act v a.round ∧
          a = (Protocol.NamedRecord.create n.record input).2 ∧
          Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing a.round
            (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) =
              some source.erase ∧
          input.fields = some ((n.st.core.σ source.erase).h,
            (n.st.core.σ source.erase).T_h.root, (n.st.core.σ source.erase).nj) ∧
          h = (n.st.core.σ source.erase).h ∧
          T = (n.st.core.σ source.erase).T_h.root ∧
          entry.erase = (n.st.core.σ source.erase).T_h ∧
          NamedBlock.Preceq entry source ∧
          (Protocol.derive_named S.E S.cfg entry).h =
            (Protocol.derive_named S.E S.cfg source).h ∧
          entry.root = T ∧ NamedBlock.Preceq entry C) ∧
    (∀ (i : Nat) (v : V), v ∈ rho.honest → i ≤ n →
      ∃ F : NamedBlock V,
        NamedRun.blockInRun S rho F ∧
        F ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
        F.erase = (NamedRun.stateBefore S rho i v).st.core.F ∧
        NamedBlock.Preceq F C)

/-- The SG emission field parameterized by its input observer
(PROTOCOL.md `sec:healing-schedule`). -/
def SGVoteIdxUsing (S : Setup V) (rho : NamedRun V)
    (read : V → NamedNodeState V → Round → NamedNodeState V) (n : Nat) (C : NamedBlock V) : Prop :=
  ∀ (i : Nat) (v : V) (ta : Time) (a : NamedAttestation V),
    v ∈ rho.honest → rho.events[i]? = some (.tick v ta) →
    NamedObject.attest a ∈ NamedRun.emittedAt S rho i v ta → i < n →
    ∀ key : BlockId, a.confirmed = some key →
      let n := read v (NamedRun.stateBefore S rho i v) a.round
      ∃ K : NamedBlock V,
        NamedRun.blockInRun S rho K ∧ K ∈ n.st.bodies ∧ K.root = key ∧
        NamedBlock.Preceq K C

/-- Honest emission history reads the actual pre-attestation input, including
prior duties of the same tick (PROTOCOL.md `sec:healing-schedule`). -/
def LayerAHistoryIdx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  LayerAHistoryIdxUsing S rho (NamedActionReads.windowActionReadFrom S)
    (fun v => (S.node v).act) n C

/-- SG rows name the selected head at their actual emission input
(PROTOCOL.md `sec:healing-schedule`). -/
def SGVoteIdx (S : Setup V) (rho : NamedRun V) (n : Nat) (C : NamedBlock V) : Prop :=
  SGVoteIdxUsing S rho (NamedActionReads.windowActionReadFrom S) n C

/-- The point schedule recovers every original emission-history field
(PROTOCOL.md `sec:healing-schedule`). -/
theorem layerAHistoryIdx_point (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) (hpoint : ∀ v r, (S.node v).act r = S.a r) :
    LayerAHistoryIdx S rho n C ↔
      LayerAHistoryIdxUsing S rho (fun _ => actionReadFrom S) (fun _ => S.a) n C := by
  have hread : NamedActionReads.windowActionReadFrom S =
      (fun _ => actionReadFrom S) := by
    funext v before r
    simp only [NamedActionReads.windowActionReadFrom, hpoint,
      Proofs.WindowAction.windowReadFrom_point]
    rfl
  have hact : (fun v => (S.node v).act) = (fun _ => S.a) := by
    funext v r
    exact hpoint v r
  simp only [LayerAHistoryIdx, hread, hact]

/-- The point schedule recovers the original SG emission-history field
(PROTOCOL.md `sec:healing-schedule`). -/
theorem sgVoteIdx_point (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) (hpoint : ∀ v r, (S.node v).act r = S.a r) :
    SGVoteIdx S rho n C ↔ SGVoteIdxUsing S rho (fun _ => actionReadFrom S) n C := by
  have hread : NamedActionReads.windowActionReadFrom S =
      (fun _ => actionReadFrom S) := by
    funext v before r
    simp only [NamedActionReads.windowActionReadFrom, hpoint,
      Proofs.WindowAction.windowReadFrom_point]
    rfl
  simp only [SGVoteIdx, hread]

#print axioms layerAHistoryIdx_point
#print axioms sgVoteIdx_point

/-- Confirmation at actual action inputs lies below the history witness
(PROTOCOL.md `sec:healing-schedule`). -/
def ConfirmationIdx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  ∀ (i : Nat) (v : V) (r : Round), v ∈ rho.honest →
    rho.events[i]? = some (.tick v ((S.node v).act r)) → i < n →
    ∃ L : NamedBlock V,
      NamedRun.blockInRun S rho L ∧
      L ∈ (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      L.erase = (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∧
      NamedBlock.Preceq L C

/-! ## Provenance of a renewal witness -/

/-- A joint-history witness is either genesis, an honest live-confirmed body, or
the SG-vote body returned by an honest action read. The last arm records the
shape of `sg_vote_on_history` rather than treating an arbitrary upper bound as
a confirmation witness. -/
def WitnessProvenanceIdx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  C = .genesis ∨
    ∃ (i : Nat) (v : V) (r : Round), i ≤ n ∧ v ∈ rho.honest ∧
      rho.events[i]? = some (.tick v ((S.node v).act r)) ∧
      C ∈ (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      (C.erase = (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∨
        C.erase = Protocol.get_sg_vote_with
          (NamedProfile.gradeContract
            (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).cache)
          S.E S.hc (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.core.toHealing r
          (Protocol.grade2_block_with
            (NamedProfile.gradeContract
              (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).cache)
            S.E S.hc (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.core.toHealing r))

/-- The point schedule recovers the original ConfirmationIdx contract
(PROTOCOL.md `sec:healing-schedule`). -/
theorem confirmationIdx_point (S : Setup V) (rho : NamedRun V)
    (n : Nat) (C : NamedBlock V) (hpoint : ∀ v r, (S.node v).act r = S.a r) :
    ConfirmationIdx S rho n C ↔ (∀ (i : Nat) (v : V) (r : Round), v ∈ rho.honest →
    rho.events[i]? = some (.tick v (S.a r)) → i < n →
    ∃ L : NamedBlock V,
      NamedRun.blockInRun S rho L ∧
      L ∈ (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      L.erase = (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∧
      NamedBlock.Preceq L C) := by
  simp only [ConfirmationIdx, NamedActionReads.windowActionReadFrom, hpoint,
    Proofs.WindowAction.windowReadFrom_point, actionReadFrom]

#print axioms confirmationIdx_point

/-- The point schedule recovers the original WitnessProvenanceIdx contract
(PROTOCOL.md `sec:healing-schedule`). -/
theorem witnessProvenanceIdx_point (S : Setup V) (rho : NamedRun V)
    (n : Nat) (C : NamedBlock V) (hpoint : ∀ v r, (S.node v).act r = S.a r) :
    WitnessProvenanceIdx S rho n C ↔ (C = .genesis ∨
    ∃ (i : Nat) (v : V) (r : Round), i ≤ n ∧ v ∈ rho.honest ∧
      rho.events[i]? = some (.tick v (S.a r)) ∧
      C ∈ (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      (C.erase = (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∨
        C.erase = Protocol.get_sg_vote_with
          (NamedProfile.gradeContract
            (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
          S.E S.hc (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r
          (Protocol.grade2_block_with
            (NamedProfile.gradeContract
              (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
            S.E S.hc (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r))) := by
  simp only [WitnessProvenanceIdx, NamedActionReads.windowActionReadFrom, hpoint,
    Proofs.WindowAction.windowReadFrom_point, actionReadFrom]

#print axioms witnessProvenanceIdx_point

/-- The index-bounded joint history, one witness. -/
def LayerAJointHistoryIdx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  LayerAHistoryIdx S rho n C ∧ SGVoteIdx S rho n C ∧ ConfirmationIdx S rho n C ∧
    WitnessProvenanceIdx S rho n C

/-- Events with time at most `t` form a prefix of the sorted list; `boundaryIdx`
is its length (the `≤ t` boundary). -/
def boundaryIdx (rho : NamedRun V) (t : Time) : Nat :=
  (rho.events.filter fun e => decide (e.time ≤ t)).length



end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
