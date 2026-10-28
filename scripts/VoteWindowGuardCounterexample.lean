import DecoupledConsensusModel.Protocol.Tick
open DecoupledConsensusModel Protocol Execution

-- The generalized scheduler can emit at zero for a node outside Setup.act_eq.
example {V : Type} [DecidableEq V] [Fintype V]
    (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Node V) (st : NamedStore V)
    (record : NamedRecord) (hs : E.slotOf 0 = 0)
    (ha : nd.act 0 = 0) (hw : nd.awake 0 = true) :
    (NamedTick.tick gc E hc cfg nd st record 0).2.2.length = 1 := by
  simp [NamedTick.tick, TickScheduler.runWith, NamedTick.namedOps,
    hs, HealConfig.round_of, ha, hw]

-- The original theorem's attestation guard is false at that same instant.
example {V : Type} [DecidableEq V] [Fintype V]
    (E : Env V) (hc : HealConfig) : (0 : Time) ≠ hc.a E.Δ 0 := by
  simp [HealConfig.a, HealConfig.opening_slot, slotStart]
  exact ne_of_gt E.Δ_pos
