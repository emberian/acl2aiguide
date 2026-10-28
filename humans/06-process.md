# 6. Process: assurance without drowning in it

The previous chapters are about what to write. This one is about the order
to write it in, how much of it to write, and how to run the prover while
writing it, so that the assurance you end with is about the program you
ship and the apparatus around it stays smaller than the program.

fn is the worked example again, and on process it is mostly the cautionary
one: its anatomy at the freeze counted 1,917 books and "About 1.47M lines to
ship 108K lines of logic and 81K of host" [fn:
build/coordinator/ANATOMY-20261009.md:9, 18 @worktree]. The rules below are
the ones its record supports, each with the measurement or the incident
behind it.

Source conventions are those of chapter 5: fn at `origin/dev` =
`3bbfc4dca`, its untracked coordinator documents marked `@worktree` (read in
fn's main worktree on 2026-10-28), "the laptop" = ACL2 8.7 on SBCL 2.6.8 on
an Apple M2 Max, and the examples under `examples/process/`, each certified
before it was cited. Non-ASCII characters inside quotations are
transliterated (`{}` for the empty set, `epsilon_rbr`, `<=`, `->`, `--`).

## 6.1 Statement first

### What goes wrong

A theorem can be true, proved, and useless: vacuous because its hypotheses
cannot hold together, about a function the program does not call, or
not the property anyone needed. The prover is no help with any of these; it
proves what it is given. Two records of the cost:

- fn's process audit of its rewrite's first day found that the coordinator
  had marked three statement packets "faithful" or "approved", and that "the
  same three packets held 3, 2 and 5 false statements that Codex or a proof
  attempt found"; the bill was "10 false statements in three approved
  packets cost three Codex rounds, two packet revisions each for A and C, and
  one 52-minute Sonnet run to find the same five that Codex had found" [fn:
  build/coordinator/PROCESS-AUDIT-20261009.md:60, 78 @worktree].
- In minidregg (a Lean project, not ACL2, but the same failure), a
  depth-composition statement was approved by a review that "checked
  polarities and stopped", then refuted by the lane asked to prove it: "at `Z
  = {}` the hypothesis is vacuous and `epsilon_rbr := -1` slips through while the
  conclusion demands `0 <= (t+k)*(-1) < 0`". The reviewer's own reckoning:
  "I never tried to build its `satisfiable` witness -- and if I had, I'd have
  found I couldn't" [cv: b54b6026#1061].

### The rule

minidregg's law, which this guide adopts: "**Statement-first.** Every
keystone enters as a `Prop` with its ATLAS fields (satisfiable + teeth +
premise-inhabitation) BEFORE proof work starts. A wrong statement proved fast
is the expensive failure. Only a lane's top-level theorem must be
non-vacuous; it gets an adversarial audit of its statement"
[file: ~/dev/minidregg/CLAUDE.md:18-21]. fn's process audit reached
the same rule from its own numbers: "a packet is 'approved to prove' only
after each keystone has run an ACL2 `test?` counterexample search and
carries its satisfiable and teeth witnesses" [fn:
build/coordinator/PROCESS-AUDIT-20261009.md:79 @worktree].

What a keystone's statement must say is fn's "Shape of the claims": "State
preservation has the schematic form `inv(s) and permitted-event(s,e) =>
inv(next(s,e))`. Prefer total, guarded interfaces that explicitly reject
malformed events rather than assume away untrusted wire inputs. An invariant
must include meaningful initial states and reachable examples, so a theorem
is not satisfied by an empty state domain" [fn: docs/proofs.md:65-69
@3bbfc4dca]. And its subject: "The subject is the function the host calls,
or a named theorem equates them" [fn: AGENTS.md:24-25 @3bbfc4dca]. fn's
suspect detector said what no static check can see: "a theorem that is
true, non-trivial, and about the wrong subject. 'The theorem subject is the
function the host calls' is a judgment recorded by hand" [fn:
docs/proofs.md:227-230 @3bbfc4dca].

How much to demand, and of which theorems: fn's cut settled on the top. "we
only need to demonstrate that our top-level theorems are not vacuous; the
rest fall from use via that ... A lemma that turns out vacuous is an ugly
argument, not a hole in the ledger" [fn: OWED.md:13-20 @3bbfc4dca].

### The shape to copy

The book is ordered as the process is: the statement, then its witnesses,
then its teeth, then the proof. The statement is written once, as two
macros, so the witnesses evaluate the same term the theorem states
[example: examples/process/statement-first.lisp]:

```lisp
(defmacro enqueue-claim-hyps (q cap)
  `(and (true-listp ,q)          ; H1: a queue
        (natp ,cap)              ; H2: a capacity
        (<= (len ,q) ,cap)))     ; H3: the queue is within it already

(defmacro enqueue-claim-concl (x q cap)
  `(<= (len (mv-nth 1 (mv-list 2 (enqueue ,x ,q ,cap)))) ,cap))

; The premise is satisfiable, and the conclusion fires there.
(assert-event (let ((x 'c) (q '(a b)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (equal (car (mv-list 2 (enqueue x q cap))) :ok)
                     (enqueue-claim-concl x q cap))))
```

`mv-list` is there because an `assert-event` cannot evaluate `(mv-nth 1
(enqueue ...))`: a call with several values in an argument position is
refused outside a theorem ("It is illegal to invoke ENQUEUE"), and the book
keeps that draft as a `local` `must-fail` [example:
examples/process/statement-first.lisp]. fn's `defteeth` does the same rewrapping at
expansion: "every emitted assert-event's value is re-read and each call of a
function with more than one output is wrapped in (MV-LIST k ...),
definitionally the identity" [fn: books/defkeystone.lisp:55-63 @3bbfc4dca].

## 6.2 Teeth: satisfiable premise, necessary hypotheses, refuted mutants

### What goes wrong

- **A negated `must-fail` is not a counterexample.** fn's rule: "Never a
  general negated `must-fail`: it proves that the prover could not find a
  proof, which is not a counterexample, and it loops when the negation is
  unprovable rather than false" [fn: docs/proof-style.md:381-383
  @3bbfc4dca]; AGENTS.md says it in one line: "A failed proof search is not
  a counterexample" [fn: AGENTS.md:29 @3bbfc4dca]. Yet fn's own debt ledger
  asks for exactly "a must-fail book inside ACL2 (`must-fail-checked`: the
  hypothesis negated or the witness broken, the conclusion refused)" for each
  top-level theorem [fn: OWED.md:16-19 @3bbfc4dca]. This guide reads
  the two as compatible only when the `must-fail` sits beside a concrete
  violating value: the `assert-event` is the counterexample, the `must-fail`
  records that the prover also refuses, and a `must-fail` alone is a search
  that failed.
- **A mutant only an unreachable state can see proves nothing.** From the
  lane that built differential tests over fn's catalog: "a teeth run that
  mutates ONE side at a reachable version and must be caught. A teeth
  mutation visible only at an unreachable version (count+1) proves nothing"
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:17 @worktree].
- **Teeth in a book run when the book certifies, not when it is
  included.** `assert-event`'s `:on-skip-proofs` default is `nil`; "supply
  `t` to evaluate the assertion even when skipping proofs (i.e., during
  `include-book` ...)" [:doc assert-event]. A `must-fail` of a `thm` has the
  opposite problem: "proofs are generally skipped during `include-book`, and
  any `thm` will succeed if proofs are skipped", so such a form "might not be
  possible to include" unless it is `local` or written with `must-fail!`
  [books: std/testing/must-fail.lisp:17]. The `must-fail` of a `defthm` in
  the statement-first example includes cleanly, because `must-fail` is a
  `make-event` and its recorded expansion is used [example:
  examples/process/statement-first.lisp] [measured: one REPL session
  including all examples/process and examples/performance books; laptop].

### The mechanism, as fn wrote it down

"A keystone ships with a reachable non-degenerate witness and one concrete
violating value per hypothesis, each an `assert-event` on the negated
conclusion" [fn: docs/proof-style.md:349-351 @3bbfc4dca]. Then the rule for
a hypothesis with no violating value, which is where vacuity hides: "If no
violating value exists for a hypothesis, the hypothesis is unnecessary:
delete it from the theorem and say so ..., or record it open with the
reason" [fn: docs/proof-style.md:384-389 @3bbfc4dca]. Where a violating
value exists but cannot be evaluated, a `must-fail` is "only the prover's
refusal: label it in the comment block directly above it, `; teeth:
prover-refusal REASON`" [fn: docs/proof-style.md:389-394 @3bbfc4dca].

fn later made the schema a macro: `defteeth` binds the teeth "to the theorem
as the world stores it (the claim is translated and compared), runs the
positive witness and every bound witness UNDER the guards, runs a removal or
mutation logically only when its entry says `:logical "why"` (recorded in
the row and counted as debt)" [fn: docs/proof-style.md:352-358 @3bbfc4dca].
The binding is the point: "When the form runs, (implies (and H1 .. Hn) C) is
TRANSLATED in the current world and must be EQUAL to (getpropc NAME
'theorem); else the form is refused (:claim-differs, printing both)" [fn:
books/defkeystone.lisp:48-53 @3bbfc4dca]. A tooth that is not bound to the
theorem's stored formula can drift from it.

What a static reader can and cannot say about a statement is fn's suspect
detector: six shapes of tautology (closed-theory corollary, instance
corollary, reflexive conclusion, definition restated, recognizer body,
branch of definition), and its own limit, the sentence to remember: "The
absence of a flag is not evidence of strength. Teeth are" [fn:
docs/proofs.md:201-235 @3bbfc4dca].

### The shape to copy

From the statement-first example, after the witness [example:
examples/process/statement-first.lisp]:

```lisp
; Remove H3: a queue already over its capacity stays over it.
(assert-event (let ((x 'z) (q '(a b c d e)) (cap 3))
                (and (true-listp q) (natp cap)          ; H1, H2 hold
                     (not (<= (len q) cap))             ; H3 fails
                     (not (enqueue-claim-concl x q cap)))))

; A mutant conclusion ("strictly below"), refuted by a concrete value.
(assert-event (let ((x 'c) (q '(a b)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (not (< (len (mv-nth 1 (mv-list 2 (enqueue x q cap)))) cap)))))

; teeth: prover-refusal  The same mutant, as a theorem the prover refuses.
(must-fail
 (defthm enqueue-mutant-strict
   (implies (enqueue-claim-hyps q cap)
            (< (len (mv-nth 1 (enqueue x q cap))) cap))))
```

Two hypotheses needed more than an evaluation, and the example records why.
H2, `(natp cap)`, is also a conjunct of `enqueue`'s guard, so the only value
that violates it is outside the guard domain; its tooth runs under
`(with-guard-checking :none ...)` and the comment says `logical`, which is
the `:logical "why"` entry of fn's macro. H1, `(true-listp q)`, has no
violating value at all; the example proves the theorem without it
(`enqueue-stays-within-capacity-without-h1`) and says why the keystone keeps
it: it is the guard of the function the program calls [example:
examples/process/statement-first.lisp].

The deterministic-simulation example of chapter 5 has the mutant form for a
machine: a step that acknowledges before the barrier, caught by the same
seeded run at a constant, replayable place [example:
examples/performance/deterministic-simulation.lisp].

## 6.3 What to prove early, what to prove late

### What goes wrong

Two opposite failures, both in fn's record.

- **Proving before the behaviour is right.** ember, six days before the
  freeze: "i'm wondering if we can focus our efforts on at least getting the
  *semantics and behavior* of everything, right ... and sprinting past the
  assurance for a bit" [fn: build/coordinator/EMBER.md:530-534 @worktree];
  and four days later, "regarding teeth and everything else it's important to
  get the software like .... working. and then also correct/proven ;) :D
  sometimes we shouldn't do those at the same time !!!!" [fn:
  build/coordinator/EMBER.md:540-549 @worktree].
- **A representation designed for the proof.** At the freeze: "some of these
  'competing representations' (a lot of them DO just need to be deleted)
  were originally designed to make the refinement proofs easier" [fn:
  build/coordinator/EMBER.md:267-271 @worktree]. Chapter 5 (5.4) measured
  where that leads: every concrete path a proved twin of a list path, and the
  list paths still called.

### The rule

Build the behaviour; test it as a program; then prove the properties you
want assurance from, about the function the program calls. fn's refinement
ladder orders the proof side the same way, from abstract executable state
down to concrete execution, with the condition that keeps it honest: "The
program used by the host must be these definitions or a justified
refinement. An abstract model plus an independently written server is
insufficient evidence for claims about the running server" [fn:
docs/proofs.md:45-61 @3bbfc4dca].

The statement still comes first (6.1). What moves late is the proof of
anything whose subject is not yet the shipped function. The representation
is chosen for the machine and the proof adapts to it through an abstraction
(an `mbe`, an abstract stobj, a functional instance); a representation chosen
to make a proof easier is a second representation, and chapter 5 is the bill.
fn's runtime model states the analogous rule for generators: "`def-pages`,
`def-wire` and `def-machine` are generalized from the first two working
instances each, not written as prerequisites" [fn:
build/coordinator/RUNTIME-MODEL-DRAFT-20261009.md:39 @worktree].

## 6.4 Not drowning in checkers and ledgers

### What goes wrong

fn's third sin, in its anatomy's words: "**The apparatus outgrew the
organism.** ... 301K lines of registers, 45K of checkers, 130K of tests and
55K of planning prose exist so many agents could work without colliding.
The checkers are a third again the size of the host they check" [fn:
build/coordinator/ANATOMY-20261009.md:28 @worktree]. Its shape table puts
the registers in context: "planning JSON | 301K | | generated registers
committed to git; 256 of 3,908 October commits only regenerate them" [fn:
build/coordinator/ANATOMY-20261009.md:11 @worktree].

The two-week audit measured the trend. ember asked for short cycles ("is
there any way we can get the latency-to-integration to less than 3 minutes
per batch?"; "lets NOT BE EXECUTING ALL OF THIS EVERY TIME"; "evidence
archive ... deep down you know it's just cargo culted bullshit"; "FIVE MINUTE
CYCLES"), and "The coordinator's answer was to keep the apparatus: 'that
apparatus found eight real defects today, so it stays'" [fn:
build/coordinator/AUDIT-TWO-WEEKS-20261013.md:43-50 @worktree]. "Since the
freeze, 110 of the 175 lane merges (63%) are `b-` (tools, trains) or `d-`
(burndown, registers) lanes. tools grew 155.9K -> 166.4K lines and tests
544.6K -> 571.4K" [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:50
@worktree]. The collapse targets, measured: "books/ + host/: +73,775 and
-12,252 lines (net +61.5K)" from the freeze to the audit's tip, and "no item
on PLAN-20261010's collapse list has been retired, and the trend points the
other way" [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:54-73
@worktree]. The coordinator's own words in that period: "the tools and tests
keep growing because every gate I rule into existence is Python with a unit
test" [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:50 @worktree].

### What counts as evidence

fn's proof document keeps the kinds apart: "Termination admission, guard
verification, theorem proof, book certification, and platform tests are
different evidence. A certified book can still depend on trusted
facilities; disclose those explicitly" [fn: docs/proofs.md:92-95
@3bbfc4dca]. Its guard-status rule is the model for reading any register:
four states, "`verified` ..., `declared-off` ..., `default-guarded` ... and
`default-unguarded`", of which "Only `verified` is an observation;
`default-guarded` is an inference about what ACL2 did, so the ledger check
accepts only `verified` for a function cited as evidence" [fn:
docs/proofs.md:186-197 @3bbfc4dca]. In this guide's examples the observation
is made in the book, from the world, with `symbol-class` [example:
examples/performance/mbe-fixnum-loop.lisp]. And scope grows with the
program: "Each new reachable command, persistent record, transition, codec or
adapter operation adds assurance obligations. A proof about an older
component does not automatically cover a new caller or the composition
between components" [fn: docs/proofs.md:11-13 @3bbfc4dca].

### What fn kept and what it deleted

The cut's ledger states the posture: "Ledger, not gate ... ACL2
certification runs for information. A book that no longer certifies and is
not on the survivors list is deleted, not repaired; a survivor book that
breaks gets a one-line hint repair when that is cheap, else a red row here
and the work continues" [fn: OWED.md:3-9 @3bbfc4dca]. And on the cut, one
commit removed "tools/depth_check.py ..., hot_path_check.py ..., the
resilience checker framework ... and their tests", while the Makefile lost
"the reach, teeth, depth, hot_path and theory steps" [fn: commit
9d5a3f99b, an ancestor of @3bbfc4dca].

What is worth keeping, in this guide's reading of that record:

1. **One generated ledger, no typed counts.** "Theorem, root, guard and test
   counts live in the generated ledger (`python3 tools/ledger.py --stdout`)
   and nowhere else, because a number that is typed is a number that drifts.
   Prose carries the property, its hypotheses and its covered scope in one
   sentence; it does not carry counts" [fn: docs/proofs.md:36-39
   @3bbfc4dca].
2. **Teeth inside ACL2**, as `assert-event` and labelled `must-fail` in the
   books, certified with them (6.2), which is where OWED put the top-level
   theorems' debt [fn: OWED.md:11-21 @3bbfc4dca].
3. **The certify gate**: a book is green when it certifies at its current
   bytes, and nothing else is evidence. fn's version: "Certified means a
   record-toolchain cert-cache entry at the book's current closure key ... A
   commit message, a proposed theorem or passing tests are not
   certification" [fn: AGENTS.md:36-37 @3bbfc4dca].

What to delete: a checker whose rule can be stated in the logic (a hot-path
traversal as an allocation bound, 5.3), a register that restates what the
world already holds (a `fn-generated` row read from the world instead of a
mirror, 5.9), and any document whose rule has lost its checker without saying
so (proof-style section 11 still describes the deleted hot-path checker as
running in `make check` [fn: docs/proof-style.md:861 @3bbfc4dca]).

## 6.5 Sizing proofs

### What goes wrong

- **Reading the wrong number.** fn measured a theorem that took forty
  minutes: `Time: 2386.26 seconds (prove: 0.02, print: 0.00, other:
  2386.24)`. "Forty minutes, and the prover did two hundredths of a second
  of proof search. The cure for that shape is a **theory change, not a
  hint**" [fn: docs/proof-style.md:591-605 @3bbfc4dca].
- **Narrowing a theory that is not narrowed.** "An `:in-theory` hint is a
  theory *expression*, and ACL2 evaluates it against the current logical
  world --- not against the theory its parent goal was proved in" [fn:
  docs/proof-style.md:675-677 @3bbfc4dca]; a `Goal` hint's disable was undone
  under every subgoal that named its own `:in-theory`, and closing the four
  transitions once at the top of the book "took C1 from 0.42 s to 0.05 s and
  the whole book from 609.53 s to 6.54 s" [fn: docs/proof-style.md:692-698
  @3bbfc4dca]. The manual's sentence is quoted there: "This call of the
  `enable` macro enables g relative to the current-theory of the current
  logical world, not relative to the theory produced by the hint at Goal"
  [:doc hints].
- **A probe stopped by a step limit.** "An `ACL2 Error [Step-limit]` says
  the form did not finish inside `n`; it says nothing about whether the form
  closes, how it splits, or whether the change under test helped --- and the
  control run aborts in the same place for the same reason, so a comparison
  between them is not a comparison at all" [fn: docs/proof-style.md:652-657
  @3bbfc4dca]. The step-limit example shows the shape: under a limit of 20
  steps the associativity of `app` is refused with "The prover step-limit,
  which is 20 in the current context, has been exceeded", "Prover steps
  counted: More than 20" and "No checkpoints to print"; without the limit it
  is proved in 435 steps [example: examples/process/step-limit-probe.lisp]
  [measured: the same `with-prover-step-limit 20` form outside `must-fail`,
  laptop REPL; the 435 is in the book's `.cert.out`].
- **Including a book for one lemma.** fn's include-hygiene lint names the
  measured case: "`books/bp-ingress.lisp`, which took a non-local include of
  `article-properties` for a single guard hint and turned a six-minute proof
  into an 1800 s timeout, 1.92M backchain frames of which none contributed"
  [fn: docs/proofs.md:262-265 @3bbfc4dca].

### The rules fn arrived at

**Profile before you hint.** "Before hints, before `e/d`, before splitting
the book: profile it" with `accumulated-persistence`; "Frames are the cost
proxy: a rune with a large frame count and no useful application is the thing
to withdraw" [fn: docs/proof-style.md:561-582 @3bbfc4dca]. The `Time:` line
first, the subgoal count second [fn: docs/proof-style.md:591-605
@3bbfc4dca].

**The ten-second rule, measured in steps.** fn's `proof_cost.py` "holds the
ten-second rule (decision D26 ...) with two numbers that do different jobs.
**The ratchet is prover steps.** ... For fixed bytes and toolchain the count
is the same on any box at any load: books/byte-store-k0-authority-error
counted 1,488,179 steps at 6.4 s and at 14.9 s of wall on persvati" [fn:
docs/proofs.md:114-121 @3bbfc4dca]. "A baseline book fails when its steps are
more than 10 % over its row's"; seconds decide only whether a book is over
the line, and only at two jobs on a quiet box; "Steps are not converted to
seconds: the rate varies more than twofold between books" [fn:
docs/proofs.md:124-147 @3bbfc4dca]. The baseline "only shrinks", and the
way to shrink it is proof work: "never raise a timeout or weaken a
statement" [fn: docs/proofs.md:163-167 @3bbfc4dca]. The manual's own
definition of a step: "Currently, a step is counted for each call of the
system functions `rewrite` and `expand-abbreviations`. However, the steps
counted may change in future releases" [:doc set-prover-step-limit].

**Split at 800 lines, at the seam.** "Split a book over 800 lines at its
seam and keep the old name as the top (`acceptance` includes
`acceptance-alloc`)" [fn: docs/proof-style.md:411-415 @3bbfc4dca]; and
"Splitting a book must reduce total or critical-path work, never only the
per-book figure" [fn: docs/proofs.md:169-171 @3bbfc4dca].

**Prefer a new book low in the graph.** "A certificate is content-hashed
over its book and everything the book includes, so changing a book
recertifies every book that includes it ... Prefer a new book low in the
table over a new field high in it" [fn: docs/proof-style.md:445-455
@3bbfc4dca]. The generated table beside that rule shows why: `books/cbor.lisp`
had 1298 dependents of 1370 [fn: docs/proof-style.md:459-461 @3bbfc4dca].
fn's anatomy drew the conclusion at the freeze: "The cost is count, not any
one book: 1,917 books ... A tree of under 500 books makes every one of these
numbers ordinary" [fn: build/coordinator/ANATOMY-20261009.md:63
@worktree].

**One world, no twins.** fn's agent rules: "Generators ... are the design
of record; grow the generator, never hand-write a twin" [fn:
AGENTS.md:20-21 @3bbfc4dca]. The cut plan wrote it per edit: "One world
(`ruling in force` ...): this is the only catalog line LB edits" [fn:
build/coordinator/CUT-M2-PLAN-20261027.md:68 @worktree]. And the incident that
shows what the alternative looks like: a worker "reached its certify boundary
by COPYING 361 shared-closure books (190,880 lines) into
books/one-world-b-private/, because making events LOCAL inside a shared
library breaks the library's other includers"; the ruling was "delete the
forest" [fn: build/coordinator/RULINGS.md:61 @worktree].

## 6.6 When to skip proofs, honestly

The manual is unambiguous about what `skip-proofs` is: "a quick way to
introduce unsoundness". "The use of `skip-proofs` carries an implicit
promise by the user that the ensuing proof obligations are indeed theorems
of the current theory. When that is not the case, `skip-proofs` can even
allow inconsistent events to be admitted to the logic" [:doc skip-proofs].
It lists four legitimate uses during development (deferring a termination
argument, deferring guard verification, recertifying around one slow
theorem, top-down construction) and ends: "A proof script involving
`skip-proofs` should be regarded as work-in-progress, not as a completed
proof with some unproved assumptions" [:doc skip-proofs]. A certified book
may contain one only by `:skip-proofs-okp t`, which the manual calls
"contrary to the spirit of certified books", and including such a book
prints a warning that is "in fact an error if `:skip-proofs-okp` is `nil` in
the `include-book` form" [:doc skip-proofs].

fn's rule is stricter, and mechanical. The certifier scans every source for
`FORBIDDEN_FACILITIES = {"skip-proofs", "defaxiom", "defttag",
"set-raw-mode", "include-raw"}` [fn: tools/certify_books.py:108
@3bbfc4dca]; the agent rules say "No skip-proofs, defaxiom, trust tags or
:program; never weaken a theorem, lock rule or ratchet to go green; never
re-baseline; no vacuous statements" [fn: AGENTS.md:30-31 @3bbfc4dca]. The
honest form of an unproved theorem is a ledger row, not an assumed event: a
lane planning statements wrote "the repo has no precedent for an unproved
`defthm` (no `skip-proofs` toward a claim) -- file the seven as `proof-owed`
ledger items naming the theorem" [fn: build/coordinator/lanedumps/actors.md:32
@worktree], and on the cut "A book that no longer certifies ... is deleted,
not repaired; ... else a red row here and the work continues" [fn:
OWED.md:6-9 @3bbfc4dca].

The one use of skipped proofs fn kept is triage, where nothing is claimed.
ACL2's provisional certification skips proofs in its first wave so that
every book's proofs can run in one parallel second wave; fn's triage tool
used it to name every independent red in one round ("an ordinary round took
690.8 s and named one independent red with fifteen books cascading behind
it; one provisional round took 317.3 s and named four independent reds"),
and says what that is worth: "**A triage run is evidence of nothing but its
list of reds.**" [fn: docs/proofs.md:554-596 @3bbfc4dca]. The manual agrees
on the trust question: "while we believe that the provisional certification
process can be trusted, we suggest that for maximum trust, it is best for all
books in a project to be certified from scratch without the provisional
certification process" [:doc provisional-certification].

## 6.7 Running ACL2 from an agent

### What goes wrong

- **Certification as the edit loop.** fn's live-session tool opens with the
  diagnosis: "The wrong loop for proof work is `certify-book`: twenty
  minutes a closure on the farm, and a red at the bottom hides everything
  above it" [fn: tools/proof_repl.py:4-7 @3bbfc4dca]. ember's version: "we
  used to have <3 minute iteration times on this project" and "earlier in
  this project we were doing LIVE QUALIFICATION IN THE REPL and even outside
  the repl like FIVE MINUTE CYCLES" [fn: build/coordinator/EMBER.md:690-735
  @worktree].
- **A session that is stale.** "The REPL refuses to redefine a changed
  function: after editing a book or test, stop and restart the session" [fn:
  build/coordinator/lanedumps/cut-m2a-lb-continuation.md:24 @worktree].
- **A trial lemma left behind.** fn's `probe` checks a checkpoint before and
  after every attempt because "a trial theorem left behind as a rewrite rule
  would make the next attempt's step count wrong (161 steps instead of 7,313
  for the same event in the lane's live check)" [fn: docs/proofs.md:544-549
  @3bbfc4dca].
- **A timeout that reads as a failure.** A form under the shell's `timeout`
  is aborted by the signal, and ACL2 reports the event as failed and goes on
  reading: on the laptop, a guard proof cut by `timeout 120` printed `Time:
  119.49 seconds (prove: 0.00, print: 0.00, other: 119.49)`, "No checkpoints
  to print" and `FAILED`, and the same form under `timeout 240` was killed
  still running [measured: the `bench-stobj` draft of chapter 5, section
  5.2, laptop REPL]. A FAILED at your own time limit is your limit.
- **A certificate that proves nothing.** "a `.cert` lying beside a book
  proves nothing, since after a merge it can be the previous source's
  certificate" [fn: docs/proofs.md:299-302 @3bbfc4dca].

### One session that stays alive

fn's `proof_repl.py` is the design to copy, whatever the tool: "one ACL2
process with the book's certified dependencies included from the cache --
seconds -- and the book's own events loaded up to the one that fails, where
each `defthm` attempt costs what the prover spends on it and nothing else"
[fn: tools/proof_repl.py:7-10 @3bbfc4dca]. Its commands, from
`docs/proofs.md` [fn: docs/proofs.md:489-552 @3bbfc4dca]:

- `start NAME BOOK --upto EVENT` installs the certified closure, starts ACL2
  and "loads the book's forms up to the named event, stopping at the first
  one ACL2 refuses";
- `send NAME FORM` "delivers one form and answers with the key checkpoints
  and the summary", "an event wrapped in `with-prover-time-limit` so a search
  that stops returning costs a minute, not the session";
- `send-range NAME BOOK --from EVENT --until EVENT` sends a stretch "with one
  cost line per form and the totals";
- `probe NAME EVENT [--hints H]` "proves a renamed copy of an event in a
  second session loaded up to just before it, leaving the first where it
  was";
- every answer "carries ACL2's own `Time:` and prover-step count for the
  form, which do not move with the box's load as elapsed seconds do";
- an idle timeout (20 minutes by default) stops a session nobody is using,
  after "hbox's 22 slots were held mostly by idle sessions under the old
  2-hour default".

And the boundary of what it proves: "A form ACL2 admits there is not a
certificate; the event goes into the book and the book certifies" [fn:
docs/proofs.md:505-506 @3bbfc4dca]. With plain ACL2, the same loop is a
REPL fed batches of forms under `timeout`, with `with-prover-time-limit` on
each event; the manual's form is `(with-prover-time-limit time form)`, where
"if the time for evaluation of `form` exceeds the value specified by `time`,
and if ACL2 notices this fact during a proof, then that proof will abort"
[:doc with-prover-time-limit]. The step-limit example wraps its proved event
that way [example: examples/process/step-limit-probe.lisp].

### Certificates and caches

fn's rules, each "paid for by a poisoned cache" [fn: docs/proofs.md:295-299
@3bbfc4dca]:

- Set `ACL2_BOOK_HASH_ALISTP=NIL`, "so ACL2 8.7 hashes book *contents*
  rather than write dates and absolute paths: a `.cert`/`.port` pair is valid
  in any worktree and on any host whose book content matches" [fn:
  docs/proofs.md:295-298 @3bbfc4dca].
- "**the key is the closure**: a certificate is valid only for a book *and
  every book it includes*" [fn: docs/proofs.md:308-312 @3bbfc4dca].
- "**The compiled file travels with the pair** ...: ACL2 on SBCL writes
  `book.fasl` after the certificate and include-book loads it only when it is
  not older than the `.cert`, so a book installed with a pair alone loads
  uncompiled" [fn: docs/proofs.md:351-355 @3bbfc4dca].
- A failed certification can still exit 0: "the certify driver ends in
  `(quit)`, which ACL2 reaches whether or not the inner `ld` returned on a
  failed `certify-book`, so a book that failed still exits 0" [fn:
  docs/proofs.md:607-611 @3bbfc4dca]. Read the verdict, not the exit code.

### The habits the transcripts measured

From fn's continuation files and process audit:

- **Never wait in the foreground.** On the rewrite's first day, two
  integrator seats "spent 5.4 h of 10.4 h in 77 calls over 60 s (most of them
  `until grep ... ; do sleep 15` loops ...)"; the seats that used a
  background job and a monitor "spent 0.04 h and 0 h waiting" [fn:
  build/coordinator/PROCESS-AUDIT-20261009.md:66 @worktree]. The whole
  forest: "Foreground waits 7.3 h of 22.9 h seat time (32%)" [fn:
  build/coordinator/PROCESS-AUDIT-20261009.md:11 @worktree]. Rule: anything
  that runs longer than a tool call's limit runs in the background, and the
  agent returns to work; the lane record's version is "`send-file` of a long
  run exceeds a 120 s tool timeout: run it in the background" [fn:
  build/coordinator/lanedumps/cut-m2a-lb-continuation.md:25 @worktree].
- **Every background process has a PID file, and nothing is killed by
  pattern.** The same lane record ends its pitfalls with "Never a whole-disk
  `find` and never a background command without a PID file", and its status
  line confesses the case: "one stray read-only `find / -name repl8.log` ...
  started by me without a PID file) is still running; ember or the
  coordinator may stop it" [fn:
  build/coordinator/lanedumps/cut-m2a-lb-continuation.md:3, 27 @worktree].
- **Certify what you changed before you report.** fn's merge procedure: "a
  lane certifies what it changed and its test books on the farm before it
  reports" [fn: docs/proofs.md:469-471 @3bbfc4dca]; the incident behind it:
  "on 2026-09-21 `dev` had been red for a day in [four books], each committed
  by a lane that never certified it" [fn: docs/proofs.md:449-453
  @3bbfc4dca].
- **Succeed from the predecessor's own file, never from a summary.** The
  audit's target "Zero fresh-agent restarts of a live concept" held: "5
  successions ..., each from the predecessor's own continuation file ... no
  first task was one the predecessor had not named, no lost thread found"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:12 @worktree].
- **Park before the ceiling.** "A1 and C1 hit the ceiling at 1 h 51 and 1 h
  53"; the change: "a builder writes its continuation and parks at 400k, not
  790k" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:70-71 @worktree].
- **Run the gate the change touched.** "A change to a shared mechanism runs
  only part of the image gate" cost two reds that surfaced 5.6 h and 7.5 h
  later; the change: pick the gate's modules from the diff, and "A train
  whose image gate is interrupted does not push until the missing modules
  have run" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:73-75
  @worktree].

### A lock released by a trap the process replaces

This guide's own tooling supplied the last example. `examples/certify.sh`,
as first committed (`4d297e4`), took a machine-wide lock with `mkdir`, set
`trap 'rmdir "$lock" 2>/dev/null' EXIT INT TERM`, and ended with `exec perl
"$ACL2_SYSTEM_BOOKS/build/cert.pl" --acl2 "$ACL2" "$@"`. `exec` replaces the
shell, so the trap never ran and the lock directory outlived every
certification; the next `certify.sh`, from any lane, waited on it
indefinitely [measured: `examples/.cert.lock` present, with no `cert.pl`
process running, after each certification on 2026-10-28 before `ce2c34b`;
laptop]. Until the script changed, this chapter's lane removed the lock after
each of its own runs and, when no `cert.pl` was running, a lock no process
held. The script at `ce2c34b` runs `perl` without `exec`, then `rmdir`s the
lock itself and exits with `perl`'s status. The rule is general: a release
that depends on a hook in the process must not follow an `exec`.

## 6.8 The process audit, as rules

fn's process audit of 2026-10-09 measured one day of a 25-agent forest
against five targets [fn: build/coordinator/PROCESS-AUDIT-20261009.md:3-15
@worktree]. Its findings, stated as rules:

1. **Under 10% of tokens and of seat time in waiting.** Missed: 10.7% of
   tokens in poll turns and 32% of seat wall-clock in foreground waits,
   "nearly all of it the integrator's foreground `until` loops" [fn:
   build/coordinator/PROCESS-AUDIT-20261009.md:3, 11 @worktree]. Rule: wait
   in the background, on a monitor that matches one completion line.
2. **No status messages.** Held: "49 messages to the coordinator: 28 READY,
   7 BLOCKED, 5 DECISION, 4 RED, 5 park notices ... 0 status or FYI" [fn:
   build/coordinator/PROCESS-AUDIT-20261009.md:13 @worktree]. Rule: report
   on events, never on a schedule.
3. **No fresh restart of a live concept.** Held (6.7). Rule: the agent that
   holds the context does the next task.
4. **Every train non-regressing.** Held, "none green" [fn:
   build/coordinator/PROCESS-AUDIT-20261009.md:14 @worktree]. Rule: a known
   red is a named row; "A new red belongs to that batch and is fixed before
   the next merge" [fn: docs/proofs.md:474-476 @3bbfc4dca].
5. **No wall catching a lane mid-call.** Missed once: a seat "died ... on
   the weekly-limit message, 15 min into train 74", with two detached jobs
   no ledger listed [fn: build/coordinator/PROCESS-AUDIT-20261009.md:15, 82
   @worktree]. Rule: read the usage gauge before starting long work; the
   audit's version, "At 70% it finishes the train in hand and parks" [fn:
   build/coordinator/PROCESS-AUDIT-20261009.md:83 @worktree].

And the audit's one rule about statements, which belongs at the top of this
chapter as well as here: "a packet is 'approved to prove' only after each
keystone has run an ACL2 `test?` counterexample search and carries its
satisfiable and teeth witnesses" [fn:
build/coordinator/PROCESS-AUDIT-20261009.md:79 @worktree].
