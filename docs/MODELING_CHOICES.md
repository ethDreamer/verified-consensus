# Modeling choices

The paper gives the protocol in prose and pseudocode. Lean needs typed data,
total functions, and finite collections. This document lists each place where
the two differ, and each place where a stated premise replaces a physical
property.

Each heading carries a marker. **representation** means that the shape of the
data or of a definition differs while the behavior stays the same;
`docs/MODEL_MAP.md` marks the same items `different shape`, `renamed` or
`inlined`, and names the edit that removes each one. Those edits need the proofs
to be redone, and are not made. **idealization** means that a premise replaces a
physical property; each one is a declaration of
`DecoupledConsensusStatements/Generic/Conditions.lean`. Section 8 lists the
structural conditions.

Each entry has four bullets: **Paper** cites `docs/PROTOCOL.md`, **Lean** gives
the file and the declaration, **Why** gives the reason, and **Check** says what
to confirm. A path with no library prefix is under `DecoupledConsensusModel/`.

## 1 The store

### 1.1 The layer chain, then a flat store — representation

- **Paper** — section 1.1 gives the store as one flat record of 17 components.
- **Lean** — the earlier layers form an `extends` chain:
  `Protocol.GoldfishStore` (`Protocol/StoreBase.lean`), `Protocol.SGStore` and
  `Protocol.FGStore` (`Protocol/ForkChoice/Goldfish.lean`),
  `Protocol.HealingStore` (`Protocol/Grades.lean`). `Protocol.Store`
  (`Protocol/Store.lean`) is a separate flat structure of 16 fields, joined to
  the chain by the read-only projection `Protocol.Store.toHealing`.
- **Why** — the chain carries bare SG votes, the flat store carries combined
  attestations, and a Lean `extends` cannot retype a field.
- **Check** — read `toHealing` field by field. It copies every field of the earlier
  layers (`latest_stable` has no field there), changes
  only the SG pool through `Protocol.sgVote`, and leaves every write to `Store`.

### 1.2 Typed timestamp maps, and grades out of the store — representation

- **Paper** — section 1.1 gives one heterogeneous `timestamp[·]`, and three
  saved grades as store components.
- **Lean** — `Protocol.Store` holds `timestamp_block`, `timestamp_vote` and
  `timestamp_sg_vote`, each a `TimestampMap` (`Objects/Time.lean`), the SG one
  keyed by `Protocol.sgVote`. `Protocol.Frame` and `Protocol.Cache`
  (`Protocol/Grades.lean`) hold the grades, in the frames `current` and `next`,
  as a field of `Execution.NamedNodeState` (`Execution/Node.lean`).
- **Why** — Lean has no untyped key, and the pool admits one attestation per
  validator and head in a round, so the projection is injective on it. The next
  round's grade 2 completes before the round rotates, so one frame is not
  enough. The two moves make 17 paper components 16 Lean fields.
- **Check** — each read uses the map of its own kind and the same comparison
  `Protocol.stampedBefore`; readers take the aligned frame through
  `Protocol.cacheAtRound`; `Protocol.clipCache` runs after every tick and
  delivery, and `Protocol.alignRound` rebuilds no missed phase.

### 1.3 List-backed pools, committee filter at the gate — representation

- **Paper** — section 1.1 calls the pools sets, and `PROTOCOL.md#goldfish_score`
  counts committee members.
- **Lean** — `Protocol.Store.gf_votes` and `Protocol.Store.sg_votes` are lists,
  read as sets by `Protocol.Store.pool` and `Protocol.Store.sg_pool`.
  `Protocol.on_goldfish_vote_checked` (`Protocol/Handlers.lean`) rejects a vote
  from outside its slot committee, and `Protocol.raw_goldfish_score`
  (`Protocol/ForkChoice/Goldfish.lean`) applies no further filter.
- **Why** — `PROTOCOL.md#propose_block` copies pooled attestations into a block,
  and `Finset.toList` is noncomputable in Mathlib, so a set pool could not be
  copied. The model tests committee membership once, at the gate. The gate
  covers the pool only: a vote that a block carries is read from the block, and
  the delivery premise of section 6 ("Well-formed carried votes") covers it.
- **Check** — every set read goes through `pool` or `sg_pool`, and
  `PROTOCOL.md#on_goldfish_vote` and `PROTOCOL.md#on_sg_vote` reject a duplicate
  before they append, which keeps each reachable list duplicate-free.

### 1.4 The core store and the named store — representation

- **Paper** — section 1.1 holds full block and attestation payloads in one
  store.
- **Lean** — `Protocol.Store` holds the erased geometry, `Block` and
  `CombinedAttestation`. `Protocol.NamedStore` (`Protocol/Handlers.lean`) wraps
  it with `bodies` and `sg_rows`, which hold `NamedBlock` and
  `NamedAttestation` (`Objects/NamedBlocks.lean`).
- **Why** — the erased types carry what the fork choice and the grades read. The
  named types carry the signed payload, including the timeout entry target that
  erasure drops. One admission path writes both.
- **Check** — `NamedAttestation.erase` and `NamedBlock.erase` keep every field
  the erased rules read.

### 1.5 The split anti-slashing record — representation

- **Paper** — section 1.2 gives the validator record as three maps (target,
  timeout, lock) and one set, the timeout history.
- **Lean** — `Protocol.Record` holds `target`, `timeout` and `lock`;
  `Protocol.NamedRecord` holds it as `legacy` and adds `timeoutHistory`
  (`Protocol/ValidatorClient.lean`).
- **Why** — the history records the entry target that the erased timeout drops.
  `PROTOCOL.md#create_attestation` writes the map and the history in one step.
- **Check** — `PROTOCOL.md#record_attestation` and the named creator update both
  halves together.

### 1.6 At most two proposal rows per validator and round — representation

- **Paper** — `PROTOCOL.md#proposal_attestations` returns at most two
  attestations of each validator for each round, and does not say which two.
- **Lean** — `Protocol.NamedProposalRows.proposalRows`
  (`Protocol/Duties/Proposals.lean`) drops rows already on the parent chain,
  then keeps at most two distinct full rows per validator and round. The
  selected round window gives a bound of
  `2 · Fintype.card V · (η_SG + 1)` rows per proposal.
- **Why** — carried side blocks can contain arbitrarily many distinct rows
  with one validator and round, and the rule bounds the proposal. Lean fixes
  the choice left open by the paper: the first two rows in list order.
- **Check** — `capPerSigner` keeps the first two distinct rows for each key;
  `capPerSigner_length_le_keys` proves the bound of twice the number of distinct
  (validator, round) keys, and `mem_proposalRows_of_unique` keeps every selected
  honest row that is not already on the parent chain, in an admissible run. The count of keys in the round window is not a separate lemma.
- **Limits** — two distinct rows from one validator and round stay visible on
  chain, but a Byzantine validator with many variants chooses which two, and
  such a pair need not be slashable evidence. The cap bounds honest proposals
  only: the model puts no limit on the rows of a received block, counts rows
  and not bytes, and does not bound computation. A deployment at Ethereum scale
  needs aggregate signatures.

## 2 The tick

### 2.1 The tick is three steps — representation

- **Paper** — `PROTOCOL.md#on_tick` is one function.
- **Lean** — `Execution.NamedNode.tick` (`Execution/Node.lean`) completes the
  grade phases with `Protocol.onPhaseTick`, runs the duties with
  `Protocol.NamedTick.tick` (`Protocol/Tick.lean`), then clips the cache with
  `Protocol.clipCache`. The duty driver is `Protocol.TickScheduler.runWith`.
- **Why** — grade completion reads the store from before the tick, the duties
  read the completed frames, and the clip applies the new finalized block. This
  is the order of `PROTOCOL.md#on_tick`.
- **Check** — read `runWith`. Each duty branch reads the state the previous
  branch produced, and the branch order matches `PROTOCOL.md#on_tick`.

### 2.2 The awake flag suppresses one duty — idealization

- **Paper** — section 3 states that an honest validator awake in a round runs
  its attestation, and that one asleep skips it and nothing else.
- **Lean** — `Protocol.Node.awake` (`Protocol/Schedule.lean`) is read at one
  place, the attestation branch of `Protocol.TickScheduler.runWith`
  (`Protocol/Handlers.lean`).
- **Why** — an asleep validator still ticks, still receives, and still processes
  every delivered object, so its store stays current.
- **Offline validators** — the committees and the proposer schedule are free
  `Setup` data (`Env.committees`, `Env.proposer`). To encode a real run in which
  an honest validator is offline, keep it honest, set `awake` to false for the
  rounds where it is offline, remove it from the committee of each slot whose
  Goldfish vote falls while it is offline, and give each slot that it would
  propose while offline to a silent faulty validator. The model node then emits
  nothing that the real validator did not emit. Under this encoding,
  `HonestCommittees` states that in each slot committee the awake honest members
  outnumber the adversarial members, and the recurrence premises count honest
  proposers that actually propose. A returning validator is modelled as one
  that has synced every message on time; a client gets this by waiting for a
  sync before it resumes its duties. A possible refinement makes the encoding
  part of the model: an asleep validator also skips its Goldfish vote and its
  proposal, `HonestCommittees` counts the awake honest members, and the
  recurrence premises ask for awake honest proposers. It is not done.
- **Check** — search the model for `awake` and confirm the one read.

## 3 Computability and decidability

### 3.1 Executable definitions, decidable propositions — representation

- **Paper** — the pseudocode is executable, and `PROTOCOL.md#supports` and
  `PROTOCOL.md#opposes` are quantified statements.
- **Lean** — no declaration of `DecoupledConsensusModel` is `noncomputable`; the
  review surface holds three, all in the statement layer
  (`Statements.Generic.awakeIn`, `Statements.Instantiation.constants`,
  `Statements.Instantiation.recoveryRound`). `Protocol.Supports` and `Protocol.Opposes`
  (`Protocol/Grades.lean`) stay quantified propositions, with the instances
  `Protocol.supportsDecidable` and `Protocol.opposesDecidable`;
  `Protocol.positive`, `Protocol.opposing` and `Protocol.gradeBool` are the
  executable tests. `Block.pickUnique?` (`Objects/Blocks.lean`) returns `none`
  unless one element matches, and `Block.find?` and `Block.deepest?` use it.
- **Why** — an executable model runs on a fixture, and
  `DecoupledConsensusWitnesses` runs one per regime. The propositions keep the
  shape of the paper rules, and the instances keep them executable. Two raw
  `Block` values may share a root, so selection must answer without choice.
- **Check** — search the model for `noncomputable`, `partial`, `sorry` and
  `axiom`, and expect no hit. The instances add no case, and every caller of
  `find?` and `deepest?` handles `none`.

## 4 The generic execution model

### 4.1 Events happen at honest nodes only — idealization

- **Paper** — the paper gives the protocol as honest node behavior.
- **Lean** — `Generic.Event` (`Generic/Run.lean`) is a tick or a delivery at one
  node, and `Statements.Generic.ScheduleWellFormed.honest_only` requires the
  node of every event to be honest.
- **Why** — a faulty validator has no state here. It acts through the objects
  honest nodes receive, and those objects are arbitrary, except for the
  unforgeability premise below.
- **Check** — no claim quantifies over the state of a faulty node, and the
  slashing evidence reads honest stores, through
  `Statements.Instantiation.interface`.

### 4.2 Folds, emissions and handler calls — representation

- **Paper** — the paper reads a node's state at a time, a duty emits an object,
  and a handler accepts or rejects an object.
- **Lean** — all in `Generic/Run.lean`. `Generic.Run.stateBefore` folds the
  events before an index, `Generic.Run.stateBeforeTime` those with time strictly
  below `t`, `Generic.Run.readAt` those with time at or below `t`, and
  `Generic.Run.final` the whole list. `Generic.Run.emittedAt` recomputes a tick
  output from the state before the event, and `Generic.Run.emits` reads it.
  `Generic.ProtocolSpec.handles` records a handler call, which may reject;
  `Generic.Run.acceptsAt` adds the change of `Generic.ProtocolSpec.processed`
  from `false` to `true`; `Generic.ProtocolSpec.carries` is structural
  containment, with the containing object first. `Execution.spec` and `Execution.handles`
  (`Execution/Instance.lean`) bind them.
- **Why** — a read at a time must include the tick at that time, so `readAt`
  uses `≤`; a precondition must not, so `stateBeforeTime` uses `<`.
  `Generic.Event.key` orders events by time, then by phase, so a tick precedes
  the deliveries at that time. The run holds no emission list, so an emission is
  a fact about the protocol, not data a run may misstate. A guard-rejected call
  consumes nothing, and the node can accept the same object later. A claim
  reads the state after all events at its time; it says nothing about the
  states between deliveries at one time.
- **Check** — each claim uses the fold its statement needs, no premise adds
  emissions to a run, and `Statements.Generic.PartialSynchrony` uses `handlesAt`
  for its conclusion and `acceptsAt` for its relay trigger.

## 5 The environment

### 5.1 One delay bound and one GST — idealization

- **Paper** — section 3.4 gives an outage as an interval `[b₀, b₁)`, and
  synchrony resumes at `b₁`.
- **Lean** — `Generic.Env` (`Generic/Env.lean`) holds one `Δ` and one `t_GST`.
  `Statements.Generic.PartialSynchrony` bounds delivery after `t_GST`, and
  `Statements.Generic.HealthyPrefixDelivery` bounds it before a cut.
  Neither bound applies to an object that the receiver's state at the deadline
  excludes (`ProtocolSpec.excludes`): a block that conflicts with the receiver's
  finalized block. The receiver would reject that block for good, and its
  children could never meet the parent condition of a delivery.
- **Why** — the model has one asynchronous period. The outage claim places it
  at `[b₀, b₁)`: delivery is bounded before `b₀`, and again from
  `t_GST ≤ b₁`. The other claims assume nothing before GST. A run with more
  than one outage is not modelled.
- **Check** — the outage claim states delivery as healthy before `b₀` and again
  from `t_GST`, and `Δ` is strict: the premises conclude
  `t' < max t t_GST + Δ`: an object sent before GST arrives before
  `t_GST + Δ`.

### 5.2 A round-sampled awake profile, read in continuous time — representation

- **Paper** — section 3 makes participation an input for each round.
- **Lean** — `Protocol.Node.awake` takes a round and `Generic.Env.awake` takes a
  time. `Statements.Instantiation.env` binds the second to the first through
  `Statements.Instantiation.actionRound`
  (`DecoupledConsensusStatements/Instantiation.lean`).
- **Why** — the protocol needs the flag once each round, but the premises
  quantify over time. `actionRound` gives round `r` the half-open window
  `[a_r, a_{r+1})`, and clamps every time below `a_0` to round 0.
- **Check** — confirm the clamp. A round-0 sleepy window is not a premise:
  sampled windows start at rounds above 0, whose preceding action is in the run.
  The exception is a run shorter than `a_0 = 6Δ`: the guard `t − period ≤ horizon`
  holds at `t = period`, and the clamp then reads round 0.

### 5.3 Weights and committees stay apart — representation

- **Paper** — Goldfish counts committee members; the SG rule, the finality
  gadget and the grades count weight.
- **Lean** — `Electorate` carries the weights and `Committees` carries
  membership only (`Objects/Weights.lean`). Nothing routes a committee through
  `Electorate.weightOf`.
- **Why** — the two counting regimes must not be conflated. `Committees` states
  no size, no honesty and no overlap law; those are premises. In a deployment
  the committee election is stake-weighted, so an honest majority of the
  committee follows from an honest majority of the stake. The election is not
  modelled: `HonestCommittees` is a premise on the committee.
- **Check** — `Protocol.raw_goldfish_score` counts cardinality, while
  `Protocol.gradeBool` and `Electorate.finalityThreshold` count weight.

### 5.4 The validator set is fixed — scope

- **Paper** — the validator set and the weights are fixed for the execution.
- **Lean** — one `Electorate` for each `Setup`. The finality threshold is
  computed from it.
- **Why** — a scope choice. Activations, exits and balance changes are not
  modelled, and no claim relates certificates of different validator sets.
- **Check** — `Env.electorate` (`Objects/Parameters.lean`) is a field of the
  setup, with no time argument.

## 6 Idealizations that are premises

Each premise named here is a declaration of
`DecoupledConsensusStatements/Generic/Conditions.lean`.

**Unforgeable signatures.** The model has no cryptography.
`Statements.Generic.UnforgeableSignatures` has two clauses: `unforgeable` covers
an object a node processes directly, and `carried` covers an object that a
processed object carries. Each says that an object attributed to an honest
validator comes from an emission by that validator, at an earlier time or the
same time. Check both; the honest-never-slashed claim consumes `carried`.

**Collision-free roots.** Block roots are the model's hash identifiers, and the
`Block` inductive stays a raw datatype. `Execution.RootInjectiveBelow` and
`Execution.RootInjectiveOnAncestors` (`Execution/Setup.lean`) state collision
freedom on a named scope, and `Execution.NamedRootCollisionFree`
(`Execution/Run.lean`) packages it over the blocks one run puts in play.
`Statements.Instantiation.interface` binds it to the interface field
`idealization`, which `ExecutionValid` and `RunWellFormed` require. This premise
makes `Block.find?` act as a hash lookup. Check that the scope covers every
block a claim compares.

**Well-formed carried votes.** `PROTOCOL.md#on_block` rejects a block when one
of its carried votes is not a previous-slot vote of a committee member, or when
`B.support_votes` is not a subset of `B.votes`. The Lean block handler
(`Protocol.on_block_using`, `Protocol/Handlers.lean`) has no such guard. The
three tests are `Execution.NamedReceipt.wellFormed` (`Execution/Node.lean`), and
`Statements.Generic.DeliveryWellFormed.wire` assumes that every delivered object
passes it. The two forms agree on the runs the claims cover, because a rejected
block leaves the store unchanged. On a run outside the premise they differ: the
Lean handler admits the block, and the voter views
(`Protocol/ForkChoice/Views.lean`) then count the carried votes with no
committee test. Check that every claim that uses Goldfish counting carries
`DeliveryWellFormed`. To remove the premise, move the three tests into the
handler; this is not done.

**Honest committees.** `Statements.Generic.HonestCommittees` requires a strict
honest majority by count in every slot committee. This is a premise, not a fact
of `Committees`. Check that the claims that need Goldfish counting name it, and
that the safety claims of the finality gadget do not.

**Ticks on the public time grid.** `Statements.Generic.PublicTime` says that a
time is a natural multiple of `Δ`. The four per-slot instants are `t_s + kΔ` for
`k` in `0 … 3`, with `t_s = 4Δs`, so the public times are exactly those
multiples. `ScheduleWellFormed.tick_public` keeps every tick on the grid, and
`ScheduleWellFormed.tick_total` supplies every honest tick on the grid in
`[0, horizon]`. Check both: without `tick_total` a node could miss a duty, and
every liveness claim would fail.

**The accountable bound, as a negation.** Section 3.3 writes the bound as
`W + w(X) < 2q` for the set `X` with evidence.
`Statements.Generic.SlashableBound` says instead that no two certificates of the
run hold evidence, where the interface binds evidence to
`HasSlashableWeightBetween` (`Protocol/Evidence.lean`). The two agree, because
`HasSlashableWeightBetween` asserts a set of weight at least `2q − W`, written
additively as `2q ≤ W + w(S)` to keep natural subtraction out of the definition.
Check the direction of the inequality, and check that `SlashableBetween` permits
the two occurrences to be one attestation.

## 7 Continuous-time participation — idealization

Section 3 states each participation condition for each round whose action time
or grade completion time falls in the run. The Lean premises quantify over every
time in scope: `Statements.Generic.WindowMajority`,
`Statements.Generic.FreshMajority`, `Statements.Generic.SingleProposerRecurrence`,
`Statements.Generic.MultiProposerRecurrence` and
`Statements.Generic.StrongMultiProposerRecurrence` are continuous-time contracts, and
are therefore at least as strong as the round-sampled form. The recurrence tiers count
only the windows that end inside the run and start at or after `t₀` (tier 1)
or GST (tiers 2 and 3).

One consequence is visible in the constants. In continuous time the window
`[t + 2·period, t + gap·period]` of `StrongMultiProposerRecurrence` is a single point
at `gap = 2`, so the smallest satisfiable strong gap is 3. The finality claims
need `gap + 2 ≤ K`, so they are non-vacuous only for `K ≥ 5`, one more than the
paper's `K ≥ 4`. The finality fixture witnesses `gap = 3` at `K = 5`. Check that
each fixture in `DecoupledConsensusWitnesses` satisfies the continuous form, and
not only the samples; the fixtures use a constant awake profile, which is why
they can.

## 8 Structural conditions, not premises

These conditions live in the parameter structures. A theorem cannot state them,
and a theorem cannot avoid them. Check them in the model. Each file below is
under `DecoupledConsensusModel/`.

```text
┌──────────────────────────────┬──────────────────────────┬──────────────────────────┐
│ Condition                    │ Field                    │ File                     │
├──────────────────────────────┼──────────────────────────┼──────────────────────────┤
│ Δ > 0                        │ Env.Δ_pos                │ Objects/Parameters.lean  │
│ Δ > 0, generic environment   │ Generic.Env.Δ_pos        │ Generic/Env.lean         │
│ R ≥ 3                        │ HealConfig.R_ge_three    │ Protocol/Grades.lean     │
│ η_SG ≥ 1                     │ HealConfig.η_SG_ge_one   │ Protocol/Grades.lean     │
│ K ≥ 4                        │ HeightConfig.K_ge_four   │ Protocol/ChainState.lean │
│ D ≥ 2                        │ HeightConfig.D_ge_two    │ Protocol/ChainState.lean │
│ Timeout: whole rounds, ≥ 2R  │ Setup.timeout_rounds     │ Execution/Setup.lean     │
│ Node runs its own index      │ Setup.node_val_index     │ Execution/Setup.lean     │
│ Committee is nonempty        │ Setup.committee_nonempty │ Execution/Setup.lean     │
│ 4 ≤ R · η_SG                 │ Setup.outage_window      │ Execution/Setup.lean     │
└──────────────────────────────┴──────────────────────────┴──────────────────────────┘
```

A round is `4ΔR`, and the SG expiry window is `η_SG` rounds. `node_val_index`
ties the node record to the validator that runs it: without it a validator could
tick with another identity, and every proposer test and committee test would
read the wrong name. `committee_nonempty` and `outage_window` stop two claims
from becoming vacuous, and each also removes its parameter point from every
claim, because no `Setup` exists there (the paper allows `R = 3`, `η_SG = 1`): an empty committee makes every committee premise false,
and at `R = 3` with `η_SG = 1` the outage window is empty.

## 9 Closed-form round times — representation

- **Paper** — appendix A.11 gives the round schedule and the action time `a_r`.
- **Lean** — `Statements.Instantiation.nextRound`
  (`DecoupledConsensusStatements/Instantiation/RoundTimes.lean`) is a closed
  form: `Int.toNat (t − a₀)` divided by `Statements.Instantiation.roundPeriod`, with a
  ceiling. `Statements.Instantiation.roundAt` is its public name.
- **Why** — a closed form reduces in a proof, and it executes. The least-round
  specification does neither.
- **Check** — read `Proofs.nextRound_eq_find`
  (`DecoupledConsensusProofs/Bridge/RoundTimes.lean`), which proves the closed
  form equal to the least round whose action time is at or after `t`. This is
  the only place where the two forms must agree.

## 10 Results proved outside the bundle

Three results are proved and are not fields of `Consensus`.
`Proofs.leakFairness` says that an honest validator's current-production
attestation supplies a height contribution, and that the inactivity-leak ledger
protects it. `Proofs.voteSafetyOfClients` says that an honest validator that
follows the validator-client signing rules is never slashable.
`Proofs.heightProgress` is the height progress of the finality gadget. All three
are in `DecoupledConsensusProofs/ReviewTheorem.lean`, and each speaks about
attestation rows, ledgers or heights, which have no protocol-independent form.
Do not read them as bundle guarantees.

## 11 Public-grid vote windows

The action instant is per validator: `Node.act r`. The execution setup requires
completion of the round's grade 0 before the action (`T_r + Δ ≤ act r`),
the action before the next round opening, and delivery by the next round's
earliest grade cutoff (`act r + Δ ≤ T_{r+1} − 5Δ`). These are P1 and P2.
The strict delivery bound then puts a delivered vote strictly before that cutoff.

P3 additionally requires `∃ k : Nat, act r = (k : Time) * Δ`. The public
handler schedule in §7.2 permits ticks only at these multiples of `Δ`, and the
attestation guard tests equality with `act r`; window inequalities alone do not
make the action reachable. For example, take `Δ = 2`, `R = 3`, and
`act r = 24r + 3`. Grade 0 completes at `24r + 2`, the action remains in
round `r`, and `act r + Δ = 24r + 5 ≤ 24r + 14`, the next G2 early cutoff.
Thus P1 and P2 hold, but all action times are odd and all public ticks are even.
Such a node emits no attestations at public ticks, even when always awake.

The paper's point schedule `T_r + 6Δ` satisfies all three conditions using
`R ≥ 3`; the existing concrete witnesses retain this schedule. The public-grid
condition states an implicit property of that schedule explicitly. It does not
alter which times the scheduler may tick.

Honest-row history is causal. A carried honest row was emitted at its author's
`Node.act` no later than the carrier was processed. For a body held in
`stateBeforeTime` at a boundary, that emission is strictly before the boundary
and no earlier than the row's G0 completion. At the paper instant `S.a r`,
these bounds give `row.round ≤ r`: another validator's round-`r` row can
already be present. Before any boundary at or before round-`r` G0 completion,
P1 gives the strict bound `row.round < r`. Specializing every `Node.act r`
to `S.a r` also recovers the original strict bound at the paper instant.
The causal contract and both corollaries are proved in
`Execution/OutageProvenance.lean`. P2 separately places strict delivery of
each round's action before all of the next round's early grade cutoffs.

For example, with `Δ = 1`, `R = 3`, and `act r = 12r + 1`, an honest
round-0 row is emitted at time 1 and included in the slot-1 proposal at time 4.
It is held before `S.a 0 = 6`. A complete public tick schedule through time 6
and unforgeability both hold in the checked example
`scripts/VoteWindowRoundHistory.lean`; strict round history at time 6 would
incorrectly require `0 < 0`.

Actions can also follow the paper instant: `Δ = 1`, `R = 4`, and
`act r = 16r + 7` satisfy P1/P2/P3. Here `S.a 0 = 6 < b0 = 7`, yet a
round-0 attestation is emitted at `b0`. Consequently, a bound on the previous
paper instant alone does not make post-boundary emissions from previous
rounds impossible. `scripts/VoteWindowLateBoundary.lean` checks this case
with every public tick through time 7 and refutes the corresponding vacuous
base-case claim with only the paper-time boundary for an arbitrary candidate
prefix. This example does not supply the additional premises of an outage regime.

The vacuous base case `NamedOutageClosure.base_hpost` therefore assumes
`∀ v, (S.node v).act (r - 1) < b0`, retaining `b0` and its original
confirmation conclusion. Each validator's actions increase strictly with the
round, so this excludes every earlier-round emission at or after `b0`.
For `r > 0`, P2 and positive delay discharge the hypothesis whenever
`early E hc r .g2 ≤ b0`. In particular, the pre-boundary frame consumer's
`S.a r < b0` supplies that cutoff bound. Under the point-instance equation,
the original `S.a (r - 1) < b0` premise also implies the new hypothesis;
`base_hpost_point` checks recovery of the unchanged conclusion explicitly.

The first-included-round selector has a different timing condition: it chooses
the first positive `r` with `b0 ≤ S.a r`. This does not itself put `b0`
after round `r`'s early G2 cutoff. With the same `R = 4` window, take
`s = 0`, `r = 2`, `b0 = 23`, `b1 = 32`, and horizon 40. Formation and
retention margins, domain inclusion, the domain deadline, minimal-round
selection, and `S.a (r - 1) < b0` all hold, yet `b0 = 23 < 27`, the early
G2 cutoff, and `act (r - 1) = 23`. The diagnostic checks these timing
premises separately from any full outage-regime construction. They do not
justify the actual-action boundary hypothesis on their own.

The first-round classification separates older emissions from stragglers.
P2 implies `act v q + Δ < S.a (q + 1)`. Minimality of the selected positive
round then gives `act v q + Δ < b0` whenever `q + 1 < r`. Any prior-round
emission at or after `b0` must therefore have `q + 1 = r`; P2 gives its
deadline `send + Δ ≤ early E hc r .g2`. A receipt strictly before that
deadline is strictly before the cutoff. With the point-instance equation
and `S.a (r - 1) < b0`, there are no stragglers, recovering the vacuous base.
These facts are checked in `Execution/RoundBase.lean`, with the structural
late-edge bound in `Protocol/Schedule/VoteWindow.lean`.

The deadline classification alone does not promise receipts during an outage.
`HealthyPrefixDelivery` applies only when `send + Δ ≤ b0`, whereas
`PartialSynchrony` promises a receipt before `max send GST + Δ`. After GST
this reduces to the P2 deadline, subject to the existing horizon and exclusion
conditions; `first_round_straggler_handles_after_gst` proves that connection.
Inside the asynchronous interval the bounds can differ: with send time 23,
`GST = b1 = 32`, and early G2 cutoff 27, P2 gives `24 ≤ 27`, but a receipt
at 32 satisfies the partial-synchrony bound `32 < 33`. Healthy-prefix delivery
does not apply because `24 > b0 = 23`. The diagnostic checks this deadline
gap with a valid window Setup. It does not construct a full outage run or
claim that extra honest support breaks a coverage invariant.

`first_round_straggler_handles_dichotomy` states the outage alternative
without strengthening delivery: a receipt either satisfies the strict delay
bound and precedes early G2, or is delayed but precedes `max send GST + Δ`.
Both arms retain the broadcast premise's horizon and exclusion guards. The
point-instance no-straggler lemma makes both arms vacuous.

Exclusion from the first-included-round induction does not mean exclusion
from a grade's input window. Round `r - 1` belongs to `latest_window η r`
for every positive retention length. The support predicate examines all
newer late-view tokens and requires their heads to cover the protected block.
Thus the algebraic preservation contract needs a content fact as well as
non-equivocation. `Protocol/Grades/HonestArrival.lean` proves that growing
the ready views preserves support and cannot introduce opposition when
every newly ready token covers the block and the enlarged raw view is clean.
These are conditional helper theorems, not additional outage premises;
their application to actual stragglers still requires an execution-level
producer for the content fact.

`scripts/VoteWindowStragglerCoverage.lean` checks why this condition cannot
simply be omitted. In a one-validator grade view, a round-1 token confirms
a non-genesis block `P`; adding a round-2 token confirming genesis removes
support for `P` and introduces opposition in round 3. Both heads are known
and compatible, and the sender has only one token per round. With `Δ = 1`,
`R = 4`, `η = 2`, send time 39, and GST 48, the grade flips both for
receipt 39 (strict delay, before early G2 at 43) and receipt 45 (outage delay,
before late G2 at 47 and the network deadline 49). The diagnostic evaluates
the actual `positive`, `opposing`, and `gradeBool` definitions. It does not
construct an outage execution or prove that an honest duty can emit this
newer head under all the base invariant's premises. Its conclusion is that
timing, compatibility, and non-equivocation alone do not establish the
required monotonicity; a proof of the straggler head floor is still needed.

The pre-boundary frame clause does supply a straggler's frozen certificate.
`Protocol/Grades/StragglerFrame.lean` proves that its round `q` satisfies
`s + 1 ≤ q` and `S.a q < b0`, and hence obtains the emitter's own opening
frame from `PreBoundaryFrames`. The finalized-prefix arm carries forward by
finality monotonicity. The raw G2 arm persists to the strict read at `act v q`
by the within-round cache theorem, clipped against that read's finality.
This transport uses no delivery or included-round invariant premise.

Transport of a raw certificate is distinct from preservation of its active
FG projection. The latter needs the protected prefix either below the FG
root or in the consuming store's filtered tree, together with appropriate
finality compatibility. The existing FG non-interference proof derives these
facts from compatible entry history and a conflicting-carrier height bound.
User-record retention does not replace that derivation: the attestation
selector reads `live_confirmed`, while `latest_confirmed` and `latest_stable`
are client-facing records. `live_confirmed` may retreat to the FG root on an
ineligible confirmation walk. The G0 veto tests compatibility, so it allows
ancestors of the protected prefix as well as descendants.

`scripts/VoteWindowRecordFloor.lean` checks the local distinction. Initially
`P` is viable and is the SG vote. Adding a conflicting height-3 body removes
the height-1 `P` from the viable tree. A confirmation update with no Goldfish
majority then returns genesis as `live_confirmed` and as the SG vote, even
though both user records still equal `P`, finality is unchanged, and the raw
G0/G2 roots still equal `P`. The update is at time 42, a support cutoff in
round 2 and a permitted P2 late edge before round 3's early G2 at 43.
The supplied post-state map is not proved to be the derived map of a reachable
named store, and the example does not authenticate an arriving carrier or
instantiate an outage execution. It shows why record retention and the G0
veto alone cannot supply the missing FG-preservation step; it is not a
counterexample to the full straggler floor or the protected outage theorem.

The causal FG argument uses strict event prefixes. `WindowSignedSourceAt`
records the actual attestation input, including any proposal, vote, or
confirmation duty earlier in the same tick. Its source can therefore be a
body inserted in that tick; run scope is recovered from the post-tick store,
not assumed from the pre-tick store. At `act = S.a`, this contract is proved
equivalent to the original signed-source contract.

An accepted carrier's ancestral honest rows were emitted strictly before
its acceptance event. This includes self-proposals: their selected rows
come from the prior pool or prior bodies, and strong induction follows
those earlier acceptances. A height-crossing quorum contains an honest
signer under the existing sleepy-weight bound. The corresponding actual
signed entry and root injectivity then bound a conflicting carrier by
`h(P) + 1`. This establishes the receipt arm without an additional quorum
or delivery premise. The same strict history gives FG noninterference in
the post-event view, including the proposal stage before an attestation.

`StragglerEntryHistory.first_round_event_history` closes the two arms for
event prefixes before the first included round's G0 completion. An earlier
honest entry is compatible by the induction hypothesis. The carrier band
and justification certificates therefore preserve the emitter's FG choice;
its pre-boundary G2 frame survives preparation of the actual action input,
with finality clipping. A nonempty selected height source lies above `P`,
so the entry it signs is compatible with `P`. Pre-`b0` emissions use the
initial history. P1 excludes current-round emissions from this base domain;
the domain contains every prior-round straggler. This does not replace the
paper checkpoint or claim compatibility of current-round entries there.
The original point history and one-shot band producers are explicitly
recovered from the event contracts. The SG emitted-head floor and the
round-invariant consumers still require integration; signed-entry
compatibility alone is not an emitted-head coverage claim.

## 12 Scope of this document

This document covers the current model. It records no history of a choice, and
it omits the proof-side vocabulary of `DecoupledConsensusInternal`. Read
`docs/MODEL_MAP.md` for the item-by-item comparison with the paper,
`docs/REVIEW_GUIDE.md` for the reading order and the premise ledger, and
`docs/ARCHITECTURE.md` for the library layout.
