# 05. The host decides: policy in 620 host functions, and two lock schemes that cannot see each other

## The wound

ANATOMY's second sin: "620 host functions (16.5K lines) branch on policy with
no book deciding: lock order, cache hits, cold-wait queues, the connection
cap. owner.lisp has 163 threading and mutex sites, io.lisp 65, with names like
`verify-under-lock`, `read-held`, `accept-locked`. The books decide what the
owner does; the host decides when, under which lock, on which thread; the 52
lock keys and the failed phase-model lanes follow from that"
[fn: build/coordinator/ANATOMY-20261009.md:27 @worktree]. The read path shows
it: one mutex `*fnn-extent-lock*` beside about twenty globals, a cache that is
"a Lisp list trimmed with `subseq` ... and probed with `find-if`", cold readers
waiting on a condition variable under the same mutex: "Every one of these is a
host decision; the books see none of it"
[fn: build/coordinator/ANATOMY-20261009.md:59 @worktree]. Ember, on
2026-10-02: "our assurance story must not be very convincing if we still are
finding LOCKING ISSUES, like how do we not have whole-system compositional
correctness statements yet..?" [fn: build/coordinator/EMBER.md:524 @worktree]
[cv: adb603dc#976].

The same shape cost fn its certification lock. The hand gate scripts took
`flock` on one file per box, while "The verdict orchestrator ... kept a second
scheme of its own beside them, an atomic `mkdir` on `.verdict.lock`, and two
schemes that cannot see each other are not a lock: a verdict run and a hand
gate could certify on one box at the same time"
[fn: docs/proofs.md:424-432 @3bbfc4dca].

The storage model is the counter-example ember named on 2026-10-28: "why don't
you actually go look at our IO/storage model? you'll see that it's HIGHLY
represented in ACL2, that we explicitly attempt to reason about it"
[fn: build/coordinator/EMBER.md:421 @worktree]. The byte store is a model in
the books (lesson 21); the threading, locking and caching around it are not.

## What was done about it

- The rule was written down: "The host decides nothing the books can decide;
  a host-side decision found is a defect filed, not a convention"
  [fn: build/coordinator/RULINGS.md:17 @worktree], and lock defects that held
  the owner mutex across durable I/O were to be "split into ACL2-ordered
  quanta, no exception rows" [fn: build/coordinator/RULINGS.md:32 @worktree].
- The surgery's first step was a runtime contract: "identified actions and
  completions, one executor, three buffer ownership states with handles and
  generations, a charged work budget with continuations, the commit point"
  [fn: build/coordinator/ANATOMY-20261009.md:75 @worktree]. It exists as a
  book written once over a constrained machine: "Every effect an instance
  wants is an ACTION ... handed to an I/O worker; the worker's answer is a
  COMPLETION ..., the only kind of event this layer consumes ... An instance
  learns that an effect happened only from its completion; submission
  establishes nothing" [fn: books/runtime-contract.lisp:3-10 @3bbfc4dca]. The
  host lease from it is on the ARTICLE path at `origin/dev`
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:112 @worktree]; the
  host's own size did not move (about 76K lines after M2 against a 10K target,
  "M3 owes about 66K host lines")
  [fn: build/coordinator/CUT-M2-PLAN-20261027.md:188 @worktree].
- The lock: one `flock` file per box, which "dies with the process that
  holds it, so there is nothing to force-unlock and nothing that can go
  stale", and the orchestrator asks the box whether that lock is free and
  "refuses with the holding process named rather than queueing silently"
  [fn: docs/proofs.md:432-437 @3bbfc4dca].

## The lesson

Every decision about what happens next (which request, which lock, which
buffer, whether a cache hit counts) is a function in a book over a state the
book defines, and the host executes the action that function returns. A
guard-verified book function costs nothing extra to run: its guard is checked
on entry and "evaluation takes place using the raw Lisp code"
[:doc guard-evaluation-table], so there is no performance argument for
deciding in the host. A mutual-exclusion mechanism is one mechanism: two
locks that do not know about each other are no lock.

## The shape to copy

The action/completion boundary of `books/runtime-contract.lisp`: the book
owns slots, a buffer pool with ownership states, and the outstanding-action
table; the host is the I/O worker that turns an action into a completion
[fn: books/runtime-contract.lisp:3-34 @3bbfc4dca]. The theorems are proved
once over a constrained instance machine and obtained per machine "by
`:functional-instance` (books/def-loop.lisp's manner)"
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca] (lesson 22, and chapter
`humans/02-rewriting-theories-books.md` section 2.9.3).

For the one lock, the gate script's own lines: `exec 9>LOCK; flock 9` at the
top, held until the script exits, and `flock -n LOCK true` as the
is-it-free probe [fn: docs/proofs.md:427-435 @3bbfc4dca].
