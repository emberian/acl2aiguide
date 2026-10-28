# 11. Probes that measured nothing

## The wound

A lane (w9/dtn-e2e) "reported a finding from such a pair --- "adding
`:forward-chaining` to the bridge made it worse" --- and retracted it: both
runs had hit a 3,000,000-step limit, and the later profile showed the
retracted configuration was pointed the wrong way for an unrelated reason.
The earlier probe in the same pair also "failed" a theorem that the real
certification had already passed" [fn: docs/proof-style.md:659-664 @3bbfc4dca].
The mechanism: "An `ACL2 Error [Step-limit]` says the form did not finish
inside `n`; it says nothing about whether the form closes, how it splits, or
whether the change under test helped --- and the control run aborts in the
same place for the same reason, so a comparison between them is not a
comparison at all" [fn: docs/proof-style.md:652-657 @3bbfc4dca].

A second way a probe lies: a trial left in the world. fn's REPL probe
"keeps a checkpoint in its session ... and checks it before and after every
attempt", because "a trial theorem left behind as a rewrite rule would make
the next attempt's step count wrong (161 steps instead of 7,313 for the same
event in the lane's live check)" [fn: docs/proofs.md:544-549 @3bbfc4dca].

## What was done about it

The rule: "a probe with a step limit answers only "does this close within `n`
steps", and a `yes` is evidence while a `no` is not. To compare two
configurations, or to locate a split, run without a limit under a wall-clock
`timeout` and read the `Time:` line ... and the profile"
[fn: docs/proof-style.md:666-671 @3bbfc4dca]. The REPL wraps each sent event
in `with-prover-time-limit` "so a search that stops returning costs a minute,
not the session" [fn: docs/proofs.md:494-497 @3bbfc4dca], and `tools/acl2
--timeout 240 < driver.lsp` "terminates the child at that many seconds and
exits 124, which makes the brief's three-minute rule mechanical rather than a
PID a lane has to remember to kill" [fn: docs/proofs.md:643-645 @3bbfc4dca].
The `probe` command undoes whatever an earlier attempt left above its
checkpoint [fn: docs/proofs.md:544-546 @3bbfc4dca].

## The lesson

A step limit turns a non-terminating search into an error and nothing more:
"that value is the maximum number of prover steps permitted before an error
occurs" [:doc set-prover-step-limit]. Use it to bound a deliberate failure or
to answer "does this close within n", never to compare configurations; compare
with no prover limit under an outer wall-clock timeout, and read `Time:` and
the profile. Run every comparison from the same world: undo a trial event
before the next (`:ubt`, [:doc ubt]), or the step counts belong to different
theories.

## The shape to copy

Chapter `humans/01-logic-and-prover.md` section 1.10 shows the limits and the
pitfall, with a certified example of a 100-step abort of a theorem that the
next event proves [example: examples/prover/step-limits.lisp]. The comparison
run, one batch per configuration, with no prover limit and an outer wall-clock
limit:

    timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < probe.lsp > out.txt 2>&1

where `probe.lsp` holds the includes and then, for each configuration, its
events followed by `:ubt` through the first of them, so the next
configuration starts from the same world [:doc ubt].
