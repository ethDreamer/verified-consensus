## 2026-10-28T22:25:58Z — stage 1
STATUS: stage=1 build=red verify=dirty sorries=0 commit=2113196
Did: Added Node.act, switched the scheduler guard to it, added Setup.act_eq, and pinned all four witness nodes to the point schedule.
Added scripts/VoteWindowGuardCounterexample.lean; lake env lean scripts/VoteWindowGuardCounterexample.lean passes. Existing theorem statements and proof bodies are untouched; no axioms or sorry/admit tokens were added.
lake build fails at Protocol/Handlers/Monotone.lean:280; scripts/verify.sh also fails its build check.
Blocked: DecoupledConsensusProofs/Protocol/Handlers/Monotone.lean's private named_tick_computed_duties (and the public equation in Protocol/Schedule/NamedTick.lean) quantifies over arbitrary Node without Setup and hard-codes hc.a. Setup.act_eq is unavailable, so the required statement is false after changing the scheduler guard.
Next: Resolve the requirement conflict: permit scheduler unfolding theorem statements to use nd.act (and repair downstream proofs through Setup.act_eq), or supply a revised design. Stage 1 is incomplete; stages 2 and 3 have not begun.
Findings: With E.slotOf 0 = 0, nd.act 0 = 0, and nd.awake 0 = true, the generalized named tick emits exactly one attestation at time zero; Lean checks this in the diagnostic script. The old equation emits nothing: proposal, vote, and confirmation guards have 0 < slot, while its attestation guard requires 0 = hc.a E.Δ 0 = 6Δ, impossible since Δ > 0 (also checked). Such nodes are excluded by Setup.act_eq but included in the unchanged theorem's domain. This is a conflict with preserving every existing theorem statement, not a counterexample to consensus safety under the proposed window.

