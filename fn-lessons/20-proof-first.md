# 20. Proof-first: representations designed for the proof, and assurance before behaviour

## The wound

Some of fn's duplicate representations were designed for the proof, not for
the program. Ember, on 2026-10-09: "some of these "competing representations"
(a lot of them DO just need to be deleted) were originally designed to make
the refinement proofs easier.... but honestly maybe this whole thing is
hopeless and we really do need to light it on fire as you suggest"
[fn: build/coordinator/EMBER.md:271 @worktree] [cv: 35f3668a#1311]. The paged
catalog is one: it proves itself by simulating the old executable, and keeps
the old foundation as a field so that "the view is the old state exactly"
(lesson 03) [fn: books/catalog-paged.lisp:140-141 @3bbfc4dca].

The work itself drifted to what could be proved. Ember, 2026-10-07:
"regarding teeth and everything else it's important to get the software like
....  working. and then also correct/proven ;) :D sometimes we shouldn't do
those at the same time !!!!" [fn: build/coordinator/EMBER.md:231 @worktree]
[cv: be1e9dcf#4275]. On the rewrite's first day, one builder concept spent
"358M tokens (A1 + A2), nothing on dev" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:61 @worktree].
The coordinator's own diagnosis four days later: "the gradient points at
small, provable, non-deleting work ... Every time I ruled 'finish what's in
flight first' this week, that was the attractor talking. Even the 15:45 pivot
got translated into 'approve statements for LB and LC'"
[fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:33 @worktree]. A contract
that never relaxes made every change to a proved statement expensive: "No
weakened, vacuous or narrowed statements; a restatement implies the old one or
carries a proof-owed item with a counterexample recorded"
[fn: build/coordinator/RULINGS.md:16 @worktree].

## What was done about it

- Ember's ordering, 2026-10-14: "it's important to get the system "running
  and tested" classically before spending too too much effort on assurance,
  because the software is a moving target, and the proofs are expensive as
  hell ... the assurance isn't a *major* focus until the 5.4 series..."
  [fn: build/coordinator/EMBER.md:990-991 @worktree].
- The cut kept proofs and stopped serving them: "Proofs ride whole ... No
  proof is repaired to make a gate; a book that breaks becomes an OWED row"
  [fn: build/coordinator/CUT-M2-PLAN-20261027.md:13 @worktree], in a ledger
  that is "Ledger, not gate": "A book that no longer certifies and is not on
  the survivors list is deleted, not repaired", with non-vacuity owed once,
  at the top-level theorems [fn: OWED.md:3-21 @3bbfc4dca].
- For fn2, 2026-10-28: "i feel like our fn2 we should be *semantics-first*
  and not worry as much about the proofs until we've actually gotten the
  implementation into a state where we WANT assurance from it .... although
  we did surely learn a LOT of lessons from this development"
  [fn: build/coordinator/EMBER.md:427 @worktree].

## The lesson

Get the behaviour right first, in definitions that run, and choose
representations for the machine; then state the claims about those
definitions, and prove them. A representation introduced to ease a proof is
proof vocabulary and lives in the logic only (lesson 01's `defun-nx` view),
never as a second executable path. ACL2 supports the order directly:
functions in `:program` mode "are logically undefined but can be executed on
constants outside of deductive contexts" [:doc program], and
`verify-termination` later converts "a function from :program mode to :logic
mode" [:doc verify-termination], after which guards and theorems follow
(chapter `humans/01-logic-and-prover.md` section 1.2.2). The statement still
comes before its proof (lesson 23); what waits is the proof work, not the
statement.

## The shape to copy

One order that follows from ember's ruling, with the ACL2 event that closes
each step [measured: steps 1 and 2 on a three-line `countdown` in the laptop
REPL, ACL2 8.7: the `assert-event` passed in `:program` mode and
`verify-termination` then admitted it in `:logic` mode]:

1. Definitions in `:program` mode, exercised on concrete inputs with
   `assert-event` [:doc assert-event] [:doc program].
2. `verify-termination` on each, which admits it in `:logic` mode
   [:doc verify-termination].
3. Guards verified, so the executed code is the raw Lisp of the same
   definitions [:doc verify-guards] [:doc guard-evaluation-table].
4. The top-level claims stated with their witnesses (lesson 23), proved last.

fn's `OWED.md` is the shape for the debt in between: one row per claim with
"the claim it carried, where it lived, and the replacement path (or "none: the
code it was about is gone")" [fn: OWED.md:3-5 @3bbfc4dca].
