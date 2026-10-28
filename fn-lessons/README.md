# fn lessons, by wound

fn is "a verified NNTP node whose books decide and whose host does I/O,
serving as the persistent event log for Mini and helm"
[fn: build/coordinator/RULINGS.md:6 @worktree]. At its freeze on 2026-10-09
it was about 1.47M lines (721K of ACL2 books in 1,917 files, 81K of Lisp
host, and the rest registers, Python checkers and tests, and planning) "to
ship 108K lines of logic and 81K of host"
[fn: build/coordinator/ANATOMY-20261009.md:7-18 @worktree]. The proof volume
was not the problem; the shape was: every concept a ladder of
representations, policy decided in the host, and an apparatus larger than
the program it checked [fn: build/coordinator/ANATOMY-20261009.md:24-28 @worktree].
After a freeze, a cut and a survey of five weeks of requests that had not
stuck [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:42 @worktree],
ember decided on 2026-10-28 to rebuild it in place as fn2, "*semantics-first*
... until we've actually gotten the implementation into a state where we WANT
assurance from it", from the bottom up [fn: build/coordinator/EMBER.md:423-427 @worktree];
the old tree is frozen [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:3 @worktree].
These files are what fn paid for, one wound each, for whoever builds fn2 or
any ACL2 system of its kind.

Each lesson has four parts: the wound, with its measurement and the fn path
that shows it; what fn did about it; the lesson as a rule, with the ACL2
mechanism it rests on; and the shape to copy. `@3bbfc4dca` is fn's
`origin/dev` (2026-10-27); `@worktree` marks a coordinator document under
`build/coordinator/`, which fn's `.gitignore` excludes (line 6), read in fn's
main working tree on 2026-10-28. The prover-side mechanisms are explained in
`humans/01-logic-and-prover.md` and `humans/02-rewriting-theories-books.md`;
the lessons point there by section instead of repeating them. Shapes that fn
does not show whole are small certified books under `examples/fn-lessons/`.

## The lessons

- `01-octet-lists-twins.md`: asked for six times, the efficient
  representations landed beside the list paths (263 host conversions, a lint
  frozen at 92); a correspondence theorem licenses replacement, and a
  `defun-nx` list view cannot be called from guard-verified code.
- `02-conceptual-multiplication.md`: ladders of rungs and a POST that changes
  representation 18 times; decide one representation and one owner per datum
  before the first layer.
- `03-refined-through-the-old.md`: the paged catalog nests the old foundation
  and LB became a third catalog; prove against the logical object and add
  implementations as attachments of one generic.
- `04-defabsstobj-by-hand.md`: 285 hand obligation theorems (271 found by grep at
  dev) and the attachment restriction; obtain obligations with
  `defabsstobj-missing-events` inside a generator.
- `05-the-host-decides.md`: 620 policy-deciding host functions and two lock
  schemes that could not see each other; books decide, the host executes
  actions, one lock is one mechanism.
- `06-the-apparatus.md`: 301K lines of registers and 45K of checkers;
  checks belong in the ACL2 world, not in Python mirrors of it.
- `07-certified-but-unreached.md`: whole landings certified that no host
  build reaches; a landing is its wiring.
- `08-whole-state-recognizers.md`: a Theta(n^2) recognizer on every
  operation, and guards evaluated per native call; carry invariants through
  `mbe` and keep the host entry's guard cheap.
- `09-exported-internals.md`: 668M of 1.50G frames spent on rules other books
  exported; decide the interface in the book's last event.
- `10-time-line-and-goal-theory.md`: 2,386 s with 0.02 s of proving, and
  609 s to 6.5 s by closing a theory in the book instead of a `Goal` hint.
- `11-step-limited-probes.md`: a comparison of two step-limited aborts, and a
  probe polluted by its own trial rule; compare without a prover limit.
- `12-library-weight.md`: tau, arithmetic-5 and a crashing rule class, costs
  the step count does not see; measure wall time per book.
- `13-certificate-cache.md`: a cache poisoned twice; a certificate is
  evidence about its book's and its closure's exact bytes.
- `14-reading-green.md`: `git log`, exit codes and harness headlines read as
  green; only a certificate of the current bytes is.
- `15-triage-one-layer-per-run.md`: three lanes, 39 runs and nine hours on
  a chain of reds; provisional certification names every red in one run.
- `16-local-stobjs-and-the-repl.md`: `with-local-stobj`'s return shape, stobj
  arguments, redefinition and `loop$` badges, each an attempt lost.
- `17-wrong-depth-walks.md`: nested sessions read one level short; tagged
  levels make the short reach a guard failure.
- `18-twin-forest.md`: 361 books copied to make events `local`; change a
  library's interface in the library.
- `19-foreground-waits-and-censuses.md`: 32% of seat wall-clock waiting in
  the foreground, status censuses and summary restarts; work on events and
  keep the agent that holds the context.
- `20-proof-first.md`: representations designed for the proof and assurance
  before behaviour; semantics first, then statements, then proofs.
- `21-crash-model.md`: what the byte-store crash model covers and the 22
  behaviours it leaves out; model the environment as an adversary with named
  moves.
- `22-def-loop.md`: 850 identical inductions replaced by one bridge per shape
  and functional instantiation.
- `23-teeth.md`: ten false statements in approved packets, and the general
  negated `must-fail`; run concrete witnesses before approving a statement.
