# Task: generalize the round action time to a vote window

You are working in a Lean 4 formalization of the decoupled consensus protocol.
The paper's complete protocol (§7) is extracted verbatim in `docs/PROTOCOL.md`;
the five libraries and their roles are described in `docs/ARCHITECTURE.md`.
Read `docs/CONVENTIONS.md` and `docs/REVIEW_GUIDE.md` before writing code, and
follow them. `docs/MODELING_CHOICES.md` documents deliberate deviations from
the paper; you will add to it.

Work on the branch `vote-window`. The baseline at its branch point builds
green: `lake build` completes (~9,972 jobs) and `scripts/verify.sh` passes.
The toolchain is Lean 4.34.1 via elan (`~/.elan/bin` on PATH); the Mathlib
cache is already fetched (`lake exe cache get` has been run). The codebase
uses the Lean module system (`module`, `public import`, `@[expose] public
section`); match that style exactly.

## Background

In the paper, every validator casts its combined attestation (which carries
the SG safe vote) at one shared instant per round, `a_r = t_{rR} + 6Δ`
(`docs/PROTOCOL.md`, §6.1 `sec:healing-schedule`). The grade machinery is
calibrated to this: all round-`(r−1)` votes arrive before round `r`'s earliest
grade cutoff `T_r − 5Δ`, which is exactly the paper's `R ≥ 3` margin argument.

The executable specification being developed alongside this repo
(`ethereum/consensus-specs`, branch `decoupled-consensus`, plus the draft at
`ethDreamer/consensus-specs` branch `safe-votes`,
`specs/_features/eip8453/fork-choice.md`) instead casts safe votes across the
first `R − 2` sub-rounds of each round, one per validator, to smooth
bandwidth. The task is to prove that the paper's theorems survive this
generalization.

## The claim to establish

Replace "every validator acts at `a_r`" with "each validator `v` acts at its
own time `act v r`", subject to two premises:

- **P1 (post-completion)**: `act v r` is at or after the completion time of
  round `r`'s grade 0, which is `T_r + Δ` — every vote is cast under its own
  round's completed grades — and `act v r` lies within round `r` (so the
  scheduler's `round_of` test still identifies the round).
- **P2 (pre-cutoff)**: `act v r + Δ` is at or before round `r+1`'s grade-2
  early cutoff `T_{r+1} − 5Δ` — with the strict delivery bound (a message
  sent at `t` is received before `t + Δ`), every vote is received strictly
  before every cutoff that reads it.
- **P3 (public grid)**: `act v r` is a public time,
  `∃ k : ℕ, (node v).act r = (k : Time) * E.Δ`. The paper's §7.2 makes the
  public times the only tick times, so an off-grid action instant is
  unreachable by construction; P3 states explicitly what the paper's schedule
  satisfies implicitly. The necessity of P3 is established by the Stage 2
  diagnostic (Δ = 2, `act r = 24·r + 3` satisfies P1 ∧ P2 and never emits an
  attestation at any public tick); record that example and P3's rationale in
  `docs/MODELING_CHOICES.md`, then handle the diagnostic script per the
  standing diagnostics rule. Both intended schedule instances discharge P3 by
  arithmetic.

All existing theorems (graded delivery, confirmation safety, the healing
results, liveness, the accountable bound) must hold under P1 ∧ P2 ∧ P3 in
place of the point schedule. The paper's schedule `act v r = a_r` must be recoverable
as an instance: note that P2 for it is `a_r + Δ ≤ T_{r+1} − 5Δ`, which is
exactly the existing `R ≥ 3` inequality, so that instance must go through
using only `HealConfig.R_ge_three`.

Where proofs used "all honest validators vote the same safe value at `a_r`",
expect to need a concentration argument instead: honest validators acting at
different times within the window read different-aged confirmation states,
but under the regime's conditions those values lie on one chain, and coverage
is inherited by ancestors, so honest support still concentrates on their
deepest common prefix. If a theorem's statement appears false under the
window (not merely harder to prove), do NOT weaken the statement; record it
as a finding in `PROGRESS.md` and stop work on that theorem.

## Where the point schedule lives

- `DecoupledConsensusModel/Protocol/Grades.lean` (~line 83):
  `HealConfig.a (Δ : Time) (r : Round) : Time` — the single action instant.
- `DecoupledConsensusModel/Protocol/Handlers.lean` (~line 591), the
  `TickScheduler.runWith` guard:
  `t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧ nd.awake (...) = true` —
  the only place the protocol fires the attestation duty.
- `DecoupledConsensusModel/Protocol/Schedule.lean`: `structure Node` —
  per-validator data (`val_index`, `new_root`, `awake`); the natural home for
  `act : Round → Time`.
- `DecoupledConsensusModel/Execution/Setup.lean`: `structure Setup` — the
  standing assumptions (`timeout_rounds`, `outage_window`, …); the natural
  home for the schedule premises. `Setup.a` abbreviates the action time.
- `DecoupledConsensusStatements/Generic/Conditions.lean` and
  `Instantiation/RoundTimes.lean`, `Instantiation/OutageWindow.lean`: the
  participation premises and round timing the statements layer exposes.
- `DecoupledConsensusWitnesses/`: one satisfying run per regime; every
  regime must remain demonstrably satisfiable after your changes.

## Stages

Work in exactly these stages. Each stage ends with a green build, a clean
`scripts/verify.sh`, a commit, and a `PROGRESS.md` entry. Do not begin a
stage before the previous one is fully green.

**Stage 1 — generalize with zero semantic change.** Add `act : Round → Time`
to `Node`. Change the scheduler guard to fire on `t = nd.act r`. Add a
`Setup` field `act_eq : ∀ v r, ((S.node v).act r) = S.a r` pinning the point
schedule, and set `act := fun r => hc.a E.Δ r` at every `Node` construction
site (Witnesses included). Repair every broken proof by rewriting through
`act_eq`. Acceptance: `lake build` green, `scripts/verify.sh` clean, **zero**
`sorry`, the protected review surface (see the ground rules) byte-identical,
and internal lemmas restated only as far as the guard change requires.

*Resolution of the Stage 1 statement conflict (2026-10-28)*: lemmas that
*describe the scheduler's mechanics* — unfolding equations over an arbitrary
`Node`, such as `named_tick_computed_duties` and the public named-tick
equation — hard-code `hc.a` and are genuinely false for arbitrary `act`.
Restate them over `nd.act`: that is the correct general form. Consumers that
hold a `Setup` recover the `hc.a` form through `act_eq` at the use site. The
behavior of the generalized guard on nodes outside every regime (for example
an attestation emitted at time zero when `act 0 = 0`) is acceptable and needs
no new guard: the protected claims quantify under `Setup`, where `act_eq`
(later P1/P2) excludes such schedules. Do not add slot or time guards to the
scheduler to "fix" out-of-regime behavior.

**Stage 2 — weaken the premise to the window.** Replace `act_eq` with the
P1/P2/P3 premises as `Setup` fields (state them in the repo's `Time`
arithmetic; derive helper lemmas near `HealConfig`). P3 is authorized as
`act_public : ∀ v r, ∃ k : Nat, (S.node v).act r = (k : Time) * S.E.Δ`
(adjust to the repo's `Time` coercions as needed). Let the build surface
every proof that used point-ness; repair each. Prove the concentration lemma
where needed. Any proof you cannot close gets a tracked
`sorry` with a same-line comment `-- SORRY(vote-window): <reason>` and an
entry in `PROGRESS.md`; drive the count to zero before declaring the stage
done, or report the irreducible remainder as findings.

*Resolution of the Stage 2 history-contract question (2026-10-29)*: strict
round history at the paper instant — "honest rows held (in an ancestor)
before `S.a r` have round `< r`", as in
`Execution/OutageProvenance.lean:honest_held_ancestor_row_before_action` —
is a point-schedule artifact: it holds only because every round-`r` action
occurs simultaneously at `S.a r`. Under the window, concurrent honest
round-`r` rows legitimately appear in views before that instant; the checked
`scripts/VoteWindowRoundHistory.lean` example is accepted as establishing
this. Do NOT shrink the boundary to rescue strictness at the use sites.
Instead, restate this contract (and any internal contract of the same
strict-round-before-`S.a` shape) causally: each honest held row of round
`r′` was emitted at its emitter's `(node v′).act r′`, with the emission
preceding the hold per the repo's delivery convention, and with P1 bounding
the emission below by round-`r′` G0 completion. The round conclusion at
boundary `S.a r` weakens to `≤ r`. Derive two corollaries and use them
downstream: (a) strictness at any boundary at or before round-`r` G0
completion, where P1 excludes every round-`r` action; (b) at the point
instance, the original strict form at `S.a r`, re-derived through the causal
contract — this recovery is mandatory, as the check that no proof power is
silently lost. Downstream inductions that relied on strictness use (a) when
they genuinely need only pre-round-`r` information, and otherwise the causal
form plus the P2 delivery bound (every round-`r` action arrives before round
`r+1`'s early cutoff). Record the restatement and the example in
`docs/MODELING_CHOICES.md`, and handle the diagnostic script per the
standing diagnostics rule. If a protected statement turns out to genuinely
require strict round history at `S.a r`, stop and report it as a finding
rather than weakening anything.

*Resolution of the Stage 2 base-case question (2026-10-29)*: the
`Execution/RoundBase.lean:base_hpost` blocker is the mirror image of the
history-contract one, and gets the mirror-image answer: the paper instant
`S.a (r−1)` is not a valid boundary marker in this direction either. Its
hypothesis `S.a (r−1) < b0` bought the conclusion by vacuity only because
simultaneity made `S.a (r−1)` the unique prior-round emission time; under
the window, actions also fall after the instant (your
`scripts/VoteWindowLateBoundary.lean` example is accepted as establishing
this). Restate the boundary hypothesis against the actual actions — the
per-validator form `∀ v, (S.node v).act (r−1) < b0`, or its
delivery-completed variant if that is what the body consumes — keeping `b0`
and the conclusion's shape fixed, so the vacuity argument becomes honest
again. Alongside it, prove the discharge lemma the consumers need: the
strengthened hypothesis follows from P2 whenever `b0` is at or past round
`r`'s early G2 cutoff, which is where `stage2_preBoundaryFrames_above` and
the `StableCoverageConsumer` base invariant place their boundaries (your own
diagnostic already checks `act + Δ ≤` that cutoff). Do not invent a new
non-vacuous confirmation claim from the outage premises unless a consumer's
`b0` genuinely sits below the delivery-complete point — and if one does,
stop and report it as a finding, because that would mean the outage argument
itself leans on simultaneity. The point instance must again recover the
original form: under `act = S.a`, the old hypothesis implies the new one, so
existing instantiations go through unchanged; check this explicitly. Record
the restatement and the example in `docs/MODELING_CHOICES.md` and handle the
diagnostic per the standing rule.

*Resolution of the Stage 2 first-included-round question (2026-10-29)*: for
the below-cutoff base in `StableCoverageConsumer`, keep `b0` and the
selection (`r` minimal positive with `b0 ≤ S.a r`) fixed, and replace the
all-rounds vacuity with a two-part classification. First prove the
structural lemma that the window's late edge of round `q` strictly precedes
round `q+1`'s paper instant: P2 bounds every action of round `q` by
`T_{q+1} − 6Δ`, while `hc.a (q+1) ≥ T_{q+1}` by definition. Chained with
the selection's minimality (`S.a q < b0` for positive `q < r`), this gives
part (i): every action of every round up to `r−2` is strictly before `b0` —
the old vacuity, recovered for all but one round. Part (ii) is direct P2:
any round-`(r−1)` action at or after `b0` is delivered before round `r`'s
early G2 cutoff, i.e. before the first grade evaluation the inductive step
performs. Rebase `roundInvariant_base'` on this classification: rounds
`≤ r−2` contribute nothing at or after `b0`, and round-`(r−1)` stragglers
are handed to the step as in-flight deliveries that the round-`r` grade
reasoning counts exactly as it counts timely round-`(r−1)` support —
graded delivery already absorbs them; additional honest support must never
weaken a coverage invariant. The point instance must again recover the old
base: under `act = S.a`, round `r−1` has no stragglers (`S.a (r−1) < b0`),
so part (ii) is vacuous and the original argument goes through; check this
explicitly. If the coverage induction genuinely cannot absorb straggler
support — if extra honest round-`(r−1)` arrivals before the cutoff break
the invariant — stop and report it as a finding, since that would be a
substantive discovery about healing under the window, not plumbing. Record
the classification and the example in `docs/MODELING_CHOICES.md` as before.

*Resolution of the straggler delivery question (2026-10-29)*: your checked
gap is accepted, and it corrects the previous paragraph: its claim that
part (ii) stragglers are "delivered before round `r`'s early G2 cutoff" is
a synchrony statement and does NOT hold during the outage window — P2
bounds the send, and only the delivery assumptions turn a send bound into
a receipt bound. That clause is superseded as follows. Do NOT add any
delivery premise stronger than the existing outage model; a straggler is a
message sent into the outage and gets outage semantics, nothing more.
Handle it by the model's own delivery dichotomy: a receipt satisfying the
strict delay bound lands before the cutoff (your proved conditional lemma)
and is absorbed by the step's graded-delivery reasoning; a receipt delayed
by the outage lands before `max(send, GST) + Δ` (your after-GST corollary)
and is handled exactly as the induction already handles every other
outage-delayed arrival. The key fact making this sufficient: round `r−1`
is not an included round, so straggler rows are inputs the coverage claim
never needs — the obligation is only that an additional honest arrival at
any permitted time preserves the invariant. Prove that preservation
(coverage monotonicity in honest arrivals) where the step needs it, rather
than any receipt-timing guarantee. Rebase `roundInvariant_base'` casewise
on this: rounds through `r−2` by the proved vacuity, round-`(r−1)`
stragglers deferred to the step under the dichotomy. The point instance
has no stragglers, so both arms are vacuous and the original base is
recovered; check this explicitly as before. If invariant preservation
under an additional honest arrival genuinely fails, stop and report it as
a finding — that would mean the healing argument depends on the absence of
honest round-`(r−1)` evidence during the outage, which would be a
substantive design discovery, not plumbing.

**Stage 3 — instantiate the compressed schedule.** Define the sub-round
assignment (index-based is fine: validator `v` acts at
`slotStart Δ (opening_slot r + (ι v % (R − 2))) + Δ` for an index function
`ι`), prove P1 ∧ P2 ∧ P3 for it by arithmetic from `R ≥ 3`, and add or adapt a
Witness so the regimes are satisfied by a run using it. Also register the
point schedule as an instance (its P1/P2 proof is the `R ≥ 3` fact). Add a
section to `docs/MODELING_CHOICES.md` describing the vote window, the two
premises, and both instances.

## Ground rules

- No new axioms. `scripts/verify.sh` checks the axiom print-out of every
  theorem; it must stay clean.
- Never modify `docs/PROTOCOL.md` — it is a verbatim paper extract.
- The protected review surface is `DecoupledConsensusStatements/**` and the
  theorem statements in `DecoupledConsensusProofs/ReviewTheorem.lean`. Do not
  change those statements; new hypotheses enter only through `Setup`/regime
  bundles, following how `timeout_rounds` and the `δ_t = (2 + e)R` family are
  handled. Internal lemmas elsewhere (`DecoupledConsensusProofs/**`,
  `DecoupledConsensusInternal/**`, and Model helper equations) may be
  restated when the generalization requires it, in the minimal way: an
  equation that hard-codes `hc.a` over an arbitrary `Node` is restated over
  `nd.act`, and `Setup`-holding consumers recover the old form via `act_eq`.
  Record every restated lemma in the `PROGRESS.md` entry that covers it.
- `Model` and `Statements` stay definition-only; proofs live in `Proofs`.
- Do not attempt the "cutoff shift" variant (schedules violating P1). It is
  explicitly out of scope; if you find yourself needing votes cast before
  grade completion, stop and record a finding.
- Commit in small logical steps with imperative subject lines (match
  `git log` style). Push to `origin` (ethDreamer/verified-consensus) after
  every `PROGRESS.md` entry.
- Diagnostic scripts (such as `scripts/VoteWindowGuardCounterexample.lean`)
  are welcome while working; before declaring a stage complete, either delete
  them or promote the fact they check into a properly-homed lemma.

## Progress reporting (mandatory, machine-readable)

Maintain an append-only `PROGRESS.md` at the repo root, committed and pushed
with each update. Append an entry at every session end, stage boundary, and
whenever blocked. Entry format, exactly:

```
## <ISO-8601 timestamp> — stage <N>
STATUS: stage=<N> build=<green|red> verify=<clean|dirty|not-run> sorries=<count> commit=<short-sha>
Did: <1-3 lines: what changed since the last entry>
Blocked: <none, or the precise lemma/file and why>
Next: <1-2 lines>
Findings: <none, or anything suggesting a design flaw, a false statement, or a premise gap>
```

The `STATUS:` line must be grep-able and truthful. The acceptance checks an
independent reviewer will run against your claims, verbatim:

```
lake build
./scripts/verify.sh
grep -rn "SORRY(vote-window)" --include="*.lean" . | wc -l
git log --oneline origin/vote-window
```

A red build honestly reported is normal progress. A red build reported as
green, a weakened theorem, an untracked `sorry`, or a new axiom ends the
task. When in doubt about a modeling decision, write the question into
`Blocked:` and stop rather than guessing.
