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

All existing theorems (graded delivery, confirmation safety, the healing
results, liveness, the accountable bound) must hold under P1 ∧ P2 in place of
the point schedule. The paper's schedule `act v r = a_r` must be recoverable
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
`sorry`, every existing theorem statement byte-identical.

**Stage 2 — weaken the premise to the window.** Replace `act_eq` with the
P1/P2 inequalities as `Setup` fields (state them in the repo's `Time`
arithmetic; derive helper lemmas near `HealConfig`). Let the build surface
every proof that used point-ness; repair each. Prove the concentration lemma
where needed. Any proof you cannot close gets a tracked
`sorry` with a same-line comment `-- SORRY(vote-window): <reason>` and an
entry in `PROGRESS.md`; drive the count to zero before declaring the stage
done, or report the irreducible remainder as findings.

**Stage 3 — instantiate the compressed schedule.** Define the sub-round
assignment (index-based is fine: validator `v` acts at
`slotStart Δ (opening_slot r + (ι v % (R − 2))) + Δ` for an index function
`ι`), prove P1 ∧ P2 for it by arithmetic from `R ≥ 3`, and add or adapt a
Witness so the regimes are satisfied by a run using it. Also register the
point schedule as an instance (its P1/P2 proof is the `R ≥ 3` fact). Add a
section to `docs/MODELING_CHOICES.md` describing the vote window, the two
premises, and both instances.

## Ground rules

- No new axioms. `scripts/verify.sh` checks the axiom print-out of every
  theorem; it must stay clean.
- Never modify `docs/PROTOCOL.md` — it is a verbatim paper extract.
- Do not change the statement of any existing theorem. New hypotheses enter
  only through `Setup`/regime bundles, following how `timeout_rounds` and the
  `δ_t = (2 + e)R` family are handled.
- `Model` and `Statements` stay definition-only; proofs live in `Proofs`.
- Do not attempt the "cutoff shift" variant (schedules violating P1). It is
  explicitly out of scope; if you find yourself needing votes cast before
  grade completion, stop and record a finding.
- Commit in small logical steps with imperative subject lines (match
  `git log` style). Push to `origin` (ethDreamer/verified-consensus) after
  every `PROGRESS.md` entry.

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
