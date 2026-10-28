# 10. Forty minutes for two hundredths of a second of proving, and a `Goal` theory that did not hold

## The wound

On 2026-09-20 a lane spent most of its budget, twice, on one theorem of
`books/tcpcl-invariants` (`fn-tcl-drive-partition-independence`, C1), whose
summary read:

```
Time:  2386.26 seconds (prove: 0.02, print: 0.00, other: 2386.24)
```

"Forty minutes, and the prover did two hundredths of a second of proof
search. The cure for that shape is a **theory change, not a hint** ...
Reading the splitter note instead of this line cost that lane most of its
budget, twice, on two configurations that both reported the same thing"
[fn: docs/proof-style.md:595-605 @3bbfc4dca]. The profile then named the
mechanism: "a **second** whole-state recognizer (`fn-tcl-session-cheapp`)
exported with its own family of rules into a book that enables the session
vocabulary wholesale", so every goal that opened `fn-tcl-drive` triggered both
families: `FN-TCL-SESSION-CHEAPP-FACTS` at 79,623 tries and 147,539 frames
beside `FN-TCL-SESSIONP-FACTS` at 76,473 tries; "the new family did not add
to that class of work, it **doubled** it"
[fn: docs/proof-style.md:607-614 @3bbfc4dca].

The same book had the second wound. Its `Goal` hint disabled `fn-tcl-step`,
and a subgoal hint `("Subgoal *1/3" :in-theory (enable
fn-tcl-drive-is-a-result))` put it back under every subgoal of the fold, so
the profile reported `FN-TCL-STEP` at 481,747 frames; "Closing the four
transitions once, at the top of the book, took C1 from 0.42 s to 0.05 s and
the whole book from 609.53 s to 6.54 s" [fn: docs/proof-style.md:692-698 @3bbfc4dca].
Both mechanisms, and this guide's example of the second, are in chapter
`humans/01-logic-and-prover.md` sections 1.6.6 and 1.8.6
[example: examples/prover/subgoal-theory.lisp].

## What was done about it

- `tools/proof_profile.py`, "The first thing to run on a slow form": it runs
  the form in exactly the theory the book builds for it, under
  `(accumulated-persistence t)` with a step limit, and prints the rules by
  useless frames, by frames, by tries, the Summary and the first key
  checkpoint; "A lane that reaches for `minimal-theory` instead has skipped
  this step" [fn: docs/proof-style.md:561-589 @3bbfc4dca].
- The export rule in its sharpest form: "if a book exports a second
  recognizer over the same state, export its whole rule set under one
  `deftheory` name (`fn-tcl-cheap-rules`) so that a book reasoning in the
  first one can close all of it at once"
  [fn: docs/proof-style.md:614-619 @3bbfc4dca].
- `fn-deftransition` fixes the theory a transition proof runs in "AT THE
  FORM, so a later `in-theory` cannot widen it by accident"
  [fn: docs/proof-style.md:781-783 @3bbfc4dca].

## The lesson

Read the `Time:` line before anything else: `prove` near zero with `other`
large is work the rewriter is not doing, and fn's reading is that "`other` is
where forward chaining and type reasoning go"
[fn: docs/proof-style.md:593-594 @3bbfc4dca]; prover steps will not show it
either, since "a step is counted for each call of the system functions
`rewrite` and `expand-abbreviations`" [:doc set-prover-step-limit]. The cure
is to change what is enabled, found with `accumulated-persistence`, whose
statistics are frames and tries per rune [:doc accumulated-persistence]. And
a theory meant to hold for every subgoal is set with a `local` `in-theory`
event above the form, because a hint's theory is "evaluated relative to the
current ACL2 logical world, not relative to the theory of a previous goal"
[:doc hints].

## The shape to copy

The profile, then a theory event, not a hint
[fn: docs/proof-style.md:565-566 @3bbfc4dca]:

    python3 tools/proof_profile.py books/scheduler \
        fn-sched-step-preserves-statep --host hbox

Without fn's tool, the same measurement in a session is
`(accumulated-persistence t)`, the form, then
`(show-accumulated-persistence :frames-f)` for the useless frames
[:doc accumulated-persistence]. The fix that held is a book-level close of the
transitions, which fn's macro writes as
[fn: docs/proof-style.md:770-778 @3bbfc4dca]:

```lisp
(fn-deftransition-closed fn-tcl-session-closed
  (fn-tcl-sessionp fn-tcl-next fn-tcl-with-outbound))

(fn-deftransition fn-tcl-refuse-preserves-sessionp
  :statement (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
                      (fn-tcl-sessionp
                       (fn-tcl-result-session (fn-tcl-refuse s xfer-id reason now))))
  :closed (fn-tcl-session-closed)
  :opens (fn-tcl-refuse))
```
