# 1. TigerStyle's rules as declarations

Part 1 translated TigerBeetle's coding rules into ACL2 one at a time
(`humans/05-high-performance.md` section 5.7): a guard is an assertion
proved at every verified call site, a bound is a `defconst` used in the
guard and the theorems, static allocation is a fixed-size stobj. That
chapter answers "what is the ACL2 form of this rule". This one answers the
question fn2 ran into next: how do the rules stay true across a code base
that a fleet of agents writes, when every one of them is a convention that
the next function can forget?

fn2's answer, worked out in its layer A and tested by a review whose
findings this chapter cites throughout, is that each rule becomes a
**declaration whose expansion emits the guard, the bound and the theorem**.
A table is declared with `defcolumns`; the declaration emits the stobj, a
setter whose guard carries the column's width, a reader whose guard
requires a valid row, and the shape theorems. A machine is declared with
`defmachine`; the declaration emits its state enum, its budget and its
dispatch. The rule is then in one place, the generator, and a function
that does not obey it fails guard verification instead of passing review.
EXECUTION-MODEL section 5 states the intent: "The machine and column
declarations are the single source for (a) the ACL2 stobj realization, (b)
a flat ATC-compatible representation and dispatcher ... and (c) the
correspondence obligations between them" [fn:
fn2/docs/design/EXECUTION-MODEL.md:30 @127f7b877]. Of the three, (a)
exists; (b) and (c) are owed (chapter 7).

Every technique below has a small certified book in `examples/assured/`
that does not depend on fn2; fn2's own forms are cited by path and line,
never copied.

## 1.1 What goes wrong: rules as conventions

fn2's review of its own layer A, read by a senior engineer's eye on
2026-10-28, named three architectural sins, and the first two are the
failure of rules kept as conventions [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:185-187 @worktree, read
2026-10-29]:

1. **Absorb instead of assert.** "Every internal call re-validates its
   scalars at run time and answers with a keyword, and the internal callers
   then discard the keyword, setters drop values that do not fit, readers
   return a valid-looking 0, counters clamp, and a corrupt FIFO head turns
   into a livelock. TigerStyle's point, that an assertion turns a
   correctness bug into a liveness bug the operator sees, is inverted here:
   correctness bugs become silent liveness bugs nobody sees."
2. **The DSLs generate storage, not meaning.** "`defcolumns` and
   `defmachine` emit the stobjs; the meaning of what is stored lives in
   hand-typed integers and positions: enums generated and then compared as
   `0..3`, enum counts typed as `14`/`12`/`13`, 17- to 34-parameter
   positional functions ... The derived path the laws require stops at the
   `defstobj`."

The individual findings show what each looks like in code. A generated
setter "returns the core unchanged when `(not (unsigned-byte-p width
value))`": "A counter that overflows its column is not refused, not
clamped, not reported: the write simply does not happen" (finding A3).
Readers "return 0 for an out-of-range slot (0 = `:accept`, phase 0 =
`:free`) ... A zero is a valid value in every one of these columns" (A9).
`4294967295` as "none" "appears about 80 times across 15 files" (A11).
Enum consumers type their counts by hand, "`(< kind 14)`, `(< evkind 12)`
... Add an event kind and every one of these silently becomes wrong"
(A13) [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:26, 32, 39, 41
@worktree, read 2026-10-29].

None of these is an ACL2 error. Every one of those books certified. A
guard is only as strong as what it says, and a convention ("callers check
the width first") is not in any guard. The remedy the review gives for A3
is the shape of this whole chapter: "Put the width in the setter's guard
so a caller that cannot prove it fits fails guard verification; the
run-time `if` goes" [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:26
@worktree, read 2026-10-29].

## 1.2 Bounds in guards and in types

**The rule.** "Put a limit on everything ... all loops and all queues must
have a fixed upper bound" and "Use explicitly-sized types like `u32` for
everything" [paper: tigerbeetle2026-tiger-style.md, lines 96-102].

**How fn2 declares it.** A `defcolumns` column has a kind, `:u8`, `:u16`,
`:u32`, `:u60`, `:u64`, `:bool` or `(:enum NAME (keywords))`, and the
table has a `:rows-bound` [fn: fn2/books/columns.lisp:629-636, 656-673
@127f7b877]. After the review, the generated setter's guard carries the
width:

```lisp
(defun ,write (i v ,name)
  (declare (xargs :stobjs ,name
                  :guard (and ,guard (unsigned-byte-p ,width v))
                  :guard-hints (("Goal" :in-theory (disable ,wfp)))))
  (,raw-write i v ,name))
```

[fn: fn2/books/columns.lisp:488-492 @127f7b877], where `,guard` is
`(and (natp i) (,wfp ,name) (< i (,rows ,name)))`, so the reader, too,
cannot be called on a row that does not exist [fn:
fn2/books/columns.lisp:482-487 @127f7b877]. The width is a per-column
property, not a machine word: fn2 has "**no fixed word** ... Arithmetic
above `2^62` allocates in SBCL, so hot counters default to `:u60`; a
`:u64` column on a served path must record a `:why` explaining its width",
and the macro refuses a `:u64` column without one [fn:
fn2/docs/a-pool-host-sim.md:34-41 @127f7b877; fn: fn2/books/columns.lisp:671-672
@127f7b877]. A counter that could wrap gets an incarnation column beside
it: "a counter at its limit retires and the incarnation advances, never
wrapping into a previous identity" [fn: fn2/docs/a-pool-host-sim.md:48-50
@127f7b877].

**The shape to copy.** `examples/assured/columns.lisp` is the same idea in
one page: `(defcols NAME ((FIELD KIND) ...) :rows-bound B)` emits a stobj
with one resizable typed array per column, a `ROWS` scalar whose stobj
type is `(integer 0 B-1)`, a reader with the row guard and a setter with
the width guard [example: examples/assured/columns.lisp]. A caller that
has not established the width cannot be guard-verified:

```lisp
(must-fail
 (defun slots-record-len-unchecked (i n slots)
   (declare (xargs :stobjs slots
                   :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                               (natp n))))
   (slots-set-len i n slots)))
```

The failed guard conjecture's checkpoint is the width itself, `(< N
4294967296)` [measured: REPL `(include-book "columns")` then the form
above without `must-fail`, ACL2 8.7, laptop, 2026-10-29]. The caller that
certifies refuses by name at the boundary, where the value came from:

```lisp
(defun slots-record-len (i n slots)
  (declare (xargs :stobjs slots
                  :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots)))))
  (if (unsigned-byte-p 32 n)
      (let ((slots (slots-set-len i n slots))) (mv :ok slots))
    (mv :too-long slots)))
```

[example: examples/assured/columns.lisp]. The difference from the absorbing
setter is where the test lives and what happens when it fails: here once,
at the boundary, with a named answer the caller must handle; there in
every setter, with a write that silently does not happen.

**Enums carry their count.** Finding A13's remedy is "`defcolumns` emits
`*NAME-COUNT*` per enum and the enum setter's guard is `(< v
*NAME-COUNT*)`" [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:41
@worktree, read 2026-10-29]. fn2's generator at `127f7b877` emits one
constant per keyword and the two conversion functions, but no count
constant, and its enum setters still guard by the byte width only [fn:
fn2/books/columns.lisp:87-117, 481, 490 @127f7b877]. The example emits
`*slot-phase-count*` and uses it in the setter's guard [example:
examples/assured/columns.lisp]:

```lisp
(defcols slots
  ((phase (:enum slot-phase (:free :leased :borrowed :retired)))
   (gen :u60)
   (len :u32))
  :rows-bound 1024)

(assert-event (equal *slot-phase-count* 4))
(assert-event (equal *slot-phase-borrowed* 2))
```

**Relationships between constants are assertions too.** "Assert the
relationships of compile-time constants as a sanity check" [paper:
tigerbeetle2026-tiger-style.md, line 128] is `assert-event` over
`defconst`s; part 1 shows the form (`humans/05-high-performance.md`
section 5.7, [example: examples/performance/limits-as-guards.lisp]).

## 1.3 Budgets as guards and measures

**The rule.** "all loops and all queues must have a fixed upper bound to
prevent infinite loops or tail latency spikes ... Where a loop cannot
terminate (e.g. an event loop), this must be asserted" [paper:
tigerbeetle2026-tiger-style.md, lines 96-100].

**How fn2 decided it.** EXECUTION-MODEL rule 3, "Bounded everything,
simultaneously": "Every machine run has a work cap (initially 4 KiB
parsed/rendered/hashed, 32 structural steps, 4 action descriptors ...),
every turn has `H = 128` observations, `K = 64` calendar visits, `Aturn =
256` descriptors; every queue has a capacity with a named exhaustion
behaviour that is an ordinary continuation, never a crash ... Budget
exhaustion leaves a resumable continuation" [fn:
fn2/docs/design/EXECUTION-MODEL.md:17 @127f7b877].

**How fn2 declares it.** Each machine kind declares `:budget (:bytes 4096
:steps 32 :descriptors 4)` [fn: fn2/books/machines-a.lisp:21, 34, 51
@127f7b877], and `defmachine` emits a constant and a charge function that
refuses before any mutation:

```lisp
(defun ,charge (bytes steps descriptors)
  (declare (xargs :guard (and (natp bytes) (natp steps) (natp descriptors))))
  (if (and (<= bytes ,bytes) (<= steps ,steps) (<= descriptors ,descriptors))
      (mv bytes steps descriptors)
    (mv nil nil nil)))
```

with the comment "Preflight and finish use the same simultaneous caps. A
refused preflight yields before mutation" [fn:
fn2/books/machines.lisp:218-226 @127f7b877].

**The shape to copy.** In ACL2 a budget does three jobs at once, and the
example gives each its form [example: examples/assured/budget.lisp]:

- **The measure.** The run loop's measure is the remaining step budget,
  not the queue's length, so termination is proved from the budget and a
  run is bounded even when the queue is not:
  ```lisp
  (defun machine-run (queue bytes steps done)
    (declare (xargs :guard (and (itemsp queue) (natp bytes) (natp steps) (natp done))
                    :measure (nfix steps)))
    ...)
  ```
  On a 40-item queue with a 32-step budget the run answers `:idle` with 8
  items left, as the book asserts.
- **The guard.** The work step's guard is the budget it spends, `(<= want
  bytes)`, so a caller that has not run the preflight cannot be
  guard-verified; the book shows that refusal with `must-fail`.
- **The theorem.** One run from a fresh budget copies at most the declared
  cap (`one-run-within-caps`), every byte copied was charged
  (`machine-run-spends-what-it-charges`), and an item that does not fit
  yields and stays at the head of the queue
  (`machine-run-yield-keeps-head`).

TigerStyle's "the caps are loop bounds; a cost certificate per run makes
them a CPU bound" [fn: fn2/docs/design/EXECUTION-MODEL.md:17 @127f7b877]
names the limit of this: the theorem bounds what the budget counts. It
does not bound what the budget does not count, and fn2's review found the
step costs in its machines "self-declared" constants (`24`, `8`, `1`)
typed at each use, and its owed refinement's work bound "self-declared
constants (`24`, `4129`)" [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:43, 87
@worktree, read 2026-10-29]. A charge is only as honest as the count it
charges; fn2's WORK checker recomputes work from emitted records for that
reason (chapter 2).

## 1.4 No allocation after init

**The rule.** "All memory must be statically allocated at startup. **No
memory may be dynamically allocated (or freed and reallocated) after
initialization.**" [paper: tigerbeetle2026-tiger-style.md, lines
151-152].

**How fn2 declares it.** The `defcolumns` header comment: "Generated array
storage is the executable representation. The row/table views are
non-executable, and resizing belongs only to the generated init" [fn:
fn2/books/columns.lisp:1-3 @127f7b877]. The generated `NAME-INIT` is the
one function that calls the `RESIZE-` updaters [fn:
fn2/books/columns.lisp:590-594 @127f7b877]; every generated setter comes
with a `-PRESERVES-WFP` theorem, and `NAME-WFP` says every column's length
equals the row count, so no setter can change a length [fn:
fn2/books/columns.lisp:523-526, 577-580 @127f7b877]. The pool carves its
slots once: "At init the profile names size classes `((count . bytes)
...)`; the pool resizes its byte array to the sum and its slot table to the
total count ... No allocation after init; no fragmentation; a class with no
free slot answers `:exhausted`, which the caller holds as a continuation"
[fn: fn2/docs/a-pool-host-sim.md:56-59 @127f7b877].

**What "init" may size.** Ember's ruling is "No compile-time ceilings":
data limits are the operator profile's, and "structural capacities bound
active execution state only" [fn: fn2/docs/design/EXECUTION-MODEL.md:40
@127f7b877]. So init reads a profile and sizes from it. The review found
the inverse sin, profile fields that are not configurable: "`fn2-machines-profilep`
requires `run-bytes = 4096`, `run-steps = 32`, `run-descriptors = 4`; the
trace capacity is `4*(H+K)` hard-coded in `fn2-core-init`. A profile that
pretends to configure what the code fixes misleads every operator who reads
it" (A28) [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:66 @worktree,
read 2026-10-29].

**The shape to copy.** In `examples/assured/columns.lisp`, `NAME-INIT`
resizes every column and sets `ROWS`; every setter keeps `NAME-WFP` and
`ROWS`, and a run of setters keeps the shape without any proof about the
table's predicate being reopened:

```lisp
(defthm slots-two-writes-keep-shape
  (implies (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                (natp j) (< j (slots-rows slots)))
           (and (slots-wfp (slots-set-gen j g (slots-set-len i n slots)))
                (equal (slots-rows (slots-set-gen j g (slots-set-len i n slots)))
                       (slots-rows slots)))))
```

[example: examples/assured/columns.lisp]. The theorem is the logical half
of the rule. The run-time half, that nothing else conses on the served
path, is a measurement, per operation, and part 1 gives its form ("0 bytes"
over a named operation under `time$`, `humans/05-high-performance.md`
section 5.3).

## 1.5 Ownership states

**What goes wrong.** A buffer handed to the host for a send can be freed
and reused while the host still reads it; a stale handle from before a
reuse can write into the new owner's bytes. EXECUTION-MODEL rule 6:
"Receives and reads lend a writable range the core cannot inspect until
completion returns it; sends and writes lend immutable bytes whose reuse
waits for every external borrow to end (zero-copy send progress is not
release)" [fn: fn2/docs/design/EXECUTION-MODEL.md:20 @127f7b877].

**How fn2 declares it.** The ownership state is a declared enum column,
with a generation beside it:

```lisp
(defcolumns fn2-pool
  ((gen :u60) (base :u60) (cap :u32)
   (state (:enum fn2-pool-state (:free :workspace :leased-in :leased-out :handed :retired)))
   ...
```

[fn: fn2/books/pool.lisp:8-10 @127f7b877]. A handle is "`(slot,
generation, offset, length)`" [fn: fn2/docs/design/EXECUTION-MODEL.md:20
@127f7b877], and the generation check comes first: `((not (equal gen
(fn2-pool-gen slot fn2-pool))) :stale)` [fn: fn2/books/pool.lisp:49
@127f7b877]. The ownership rules are written as owed theorems with teeth:
"Every handle-taking export refuses a mismatched generation before other
decisions and preserves the identical logical pool" (`FN2-POOL-STALE`);
"Across every pool operation, a borrowed slot cannot become free or
retired, change generation, or have any backing byte changed"
(`FN2-POOL-NO-REUSE`); "Every operation preserves monotone generations and
retirement" (`FN2-POOL-GENERATION`) [fn: fn2/docs/OWED.md:12-16
@127f7b877]. They are stated, their teeth evaluate, and none is proved
(chapter 7).

**Where fn2's declaration is still weaker than the rule.** The review
found a borrow tracked as a count without its holder: "Typed edges are
counters without holders ... any caller holding the extent's `(epoch,
counter)` can drop another machine's `:borrow` or `:promised-read` and make
the extent releasable under a live reader. This is the pool's
`release-out` defect ... repeated on the durability path" (B10) [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:119 @worktree, read
2026-10-29]. An ownership state is a claim about who owns; a count says
only how many.

**The shape to copy.** `examples/assured/ownership.lisp` declares the
states as a `defcols` enum (free, leased, borrowed, retired) and proves the
three rules for its small pool: `slot-free-stale` and `slot-borrow-stale`
(a stale handle is refused and nothing changes), `slot-free-refuses-borrowed`
(no reuse while borrowed), `slot-free-generation-monotone` and
`slot-free-ok-invalidates-handle` (a successful free bumps the
generation, so every old handle is stale) [example:
examples/assured/ownership.lisp]. Its teeth run the whole story:

```lisp
(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

lease, borrow, a free refused while borrowed, return, a free that bumps the
generation to 1, and the old handle refused as stale.

## 1.6 Assert, never absorb: named stops

**What goes wrong.** The review's first finding: "`fn2-core-issue`
reserves, leases, then calls `fn2-op-set-range`, `-set-capability`,
`-set-storage`, `-set-cancel-target` and `fn2-op-enqueue` binding every
result code to `?ignored`, and returns `:ok`. If `enqueue` ever refuses ...
the caller is told the op was issued, the row stays `reserved` holding a
credit, and the pool lease is outstanding forever" (A1) [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:24 @worktree, read
2026-10-29].

**The rule.** "Assertions detect programmer errors. Unlike operating
errors, which are expected and which must be handled, assertion failures
are unexpected. The only correct way to handle corrupt code is to crash"
[paper: tigerbeetle2026-tiger-style.md, lines 103-106].

**Three shapes.** `examples/assured/named-stop.lisp` writes one `issue`
operation three ways over a core whose invariant is `free + queued = cap`
[example: examples/assured/named-stop.lisp]:

1. *Absorbing* (`issue-absorbing`): ignores the enqueue's code and answers
   `:ok`. On a state that breaks the invariant it answers `:ok`, spends the
   credit and queues nothing; the book asserts `(:ok 0 16)`.
2. *Proved* (`issue`): the internal `enqueue` has no refusal branch; its
   precondition `(< (queued core) *cap*)` is its guard, and `issue`'s
   guard, the invariant, proves it after a successful `reserve`. The
   impossible branch is deleted, not handled, and `issue-preserves-invariant`
   is a theorem.
3. *Stopped* (`issue-checked`): where the precondition cannot be proved,
   because the input comes from outside verified code, the check stays and
   its failure stops the core with a named reason:
   ```lisp
   (defun core-stop (reason core)
     (declare (xargs :stobjs core
                     :guard (and (natp reason) (< 0 reason)
                                 (< reason *stop-reason-count*))))
     (if (= (stopped core) 1)
         core
       (let* ((core (update-stopped 1 core))
              (core (update-stop-reason reason core)))
         core)))
   ```
   The first reason wins (`core-stop-keeps-first-reason`), so later fallout
   cannot overwrite the diagnostic.

The review asks for shape 2 first and shape 3 where 2 is not possible:
"Prove the post-reservation calls cannot refuse (guard them with the facts
the reservation established) and delete the dead branches, or turn a
non-`:ok` into a stop with evidence" [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:24 @worktree, read
2026-10-29]. fn2 took shape 3 for `fn2-core-issue`: each post-reservation
call now maps a refusal to its own stop reason (`*fn2-stop-reason-issue-range*`,
`-capability`, `-storage`, `-cancel-target`, `-enqueue`) and the core stops
with it [fn: fn2/books/core.lisp:250-267 @127f7b877]; `fn2-core-stop` keeps
the first reason ("First corruption wins: later cleanup cannot erase the
diagnostic") [fn: fn2/books/core.lisp:133-147 @127f7b877]; the reasons are
a declared enum of twenty-one keywords in the executor's control table [fn:
fn2/books/exec-state.lisp:6-15 @127f7b877]. Shape 3 is the honest interim:
it makes the impossible visible to the simulator, which asserts on stop
reasons (chapter 2), but each stop branch is still code that the
invariant says cannot run, and the proof that would delete it is owed.

**Where the boundary is.** The review's remedy for sin 1 is "architectural,
not local: name the boundary (host-supplied observations and descriptors
...), validate there only, and inside the core let guards and `mbt` carry
the invariants, with any residual impossibility stopping the executor with a
reason the simulator asserts on" [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:185 @worktree, read
2026-10-29]. `fn2-core-issue` still validates every scalar width at run
time on entry [fn: fn2/books/core.lisp:233-238 @127f7b877], which is right
only if it is the boundary.

**A refusal is not always corruption.** Running out is expected:
`reserve` answering `:exhausted` is a continuation the caller holds
(EXECUTION-MODEL rule 3), and the example keeps it as a plain refusal
[example: examples/assured/named-stop.lisp]. fn2 still has the third kind,
a non-exhaustion refusal in a machine, marked "TODO
R6-NONEXHAUSTION-REFUSAL: replace this retained stop with the named
close/release or evidence posture chosen by R6" [fn:
fn2/books/machines-a-run.lisp:75-78 @127f7b877].

## 1.7 `defcolumns` and `defmachine` as the worked forms

**What `defcolumns` emits.** In one `encapsulate`: the enum constants and
code/keyword functions; the `defstobj` with one array per column and the
`ROWS` scalar; per-array type facts by functional instance of one list
template ("One list template; each column instantiates it, without
repeating induction"); the record and shape facts; `NAME-WFP`; `NAME-INIT`
and its theorems; per column a reader and a setter with their type,
bound, `-PRESERVES-WFP`, `-PRESERVES-TYPE` and `-ROWS` theorems; the
non-executable row and table views; and a row in the world table
`fn2-columns` recording the declaration [fn: fn2/books/columns.lisp:17-32,
564-622 @127f7b877]. The generic template is chapter 4's subject: it is
what keeps a declaration's certify cost linear in its fields.

**What `defmachine` emits.** A machine is `defcolumns` plus: a `phase`
column of the machine's state enum, the common fields (generation,
principal, account, ready links, wait reason, deadline), the `-PUT` and
`-PUT-CORE` macros, the budget constant and charge function, the
generated `NAME-OBSERVES-P`, the row initializer, and a row in
`fn2-machine-kinds` [fn: fn2/books/machines.lisp:6-8, 203-241
@127f7b877]. Its declarations are short:

```lisp
(defmachine fn2-listener
 :states (:accepting :closing)
 :fields ((cap-index :u32) (cap-nonce :u32) (pending :u32) (stopped :bool) (event-ready :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-accept-credits profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev 4294967295) (ready-next 4294967295)
           (phase *fn2-listener-state-accepting*) (mode 1))
 :observes ((:accept-result fn2-listener-observe-accept) (:close-result fn2-listener-observe-close))
 :continuations ((:accepting fn2-listener-step) (:closing fn2-listener-step)))
```

[fn: fn2/books/machines-a.lisp:17-26 @127f7b877].

**Continuations name functions.** Before the repair, "`defmachine` is a
template engine, not a declaration. `:continuations` and `:initial` are
code fragments pasted into generated bodies and they reference the
generator's private binding names" (A23) [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:61 @worktree, read
2026-10-29]. Now each continuation is a symbol, and an initial value is a
constant or a named function of `(slot base n gen)` [fn:
fn2/books/machines.lisp:32-39 @127f7b877; fn: fn2/books/machines-a.lisp:11-15
@127f7b877]. `examples/assured/machine.lisp` makes the check explicit: its
`defmach` is a `make-event` that reads the world and refuses the
declaration unless every state has one continuation and every continuation
is an existing guard-verified function of `(steps st)`; the book refuses a
pasted form, a continuation not yet defined, and a state without a
continuation, each by `must-fail` and each for the declared reason
[example: examples/assured/machine.lisp; measured: REPL of the three
refused forms after `(include-book "machine")`, ACL2 8.7, laptop,
2026-10-29]. The dispatch the macro emits refuses an unknown phase by name
(`:bad-phase`), never by a default arm that runs something.

**Obligations that nothing states.** The review: "The table row records
`:obligations (initialization preservation frame output-correspondence
budget-progress flat-representation flat-transition)` and generates none
of them" (A23). At `127f7b877` the list is still there, but each entry must
be `:owed` or name a registered owed row or generator, checked by the
`make-event` in `defmachine`, which refuses "Unregistered or unstated
machine obligation" [fn: fn2/books/machines.lisp:174-192, 261-267
@127f7b877]. A name is not a statement; DSL-METATHEORY's plan replaces the
list with an obligation store whose rows carry their statements (chapter
6, chapter 7).

**What the forms still do not emit.** The review's A17: four copies of a
put-binding generator, "about seventeen 'preserves type/wfp/rows' macros",
four snapshot/copy/diff generators, all hand-written beside the DSL [fn:
build/coordinator/fn2/REVIEW-SINS-20261028.md:50 @worktree, read
2026-10-29]. `fn2-core-shape-lemmas` is one of them [fn:
fn2/books/core.lisp:122-131 @127f7b877]. The sentinel `4294967295` is still
spelled out in the listener's admission [fn:
fn2/books/machines-a-run.lisp:86 @127f7b877]. A declaration is finished
when its consumers need no hand-written twin of anything it could emit.

## 1.8 What a declaration cannot check

A generator checks what it is given. It cannot see a literal compared with
an enum in a consumer it did not generate, a field read by position, or a
specification function called on a served path. fn2's metatheory plan adds
eight expansion-time and assembly-time guards for exactly those sins (an
enum compared as an integer, positional access, a specification on a
served path, the absorbed refusal and the lying read among them), reading
submitted forms rather than translated bodies, because "A translated body
inlines a constant's value, so an enum comparison and a literal comparison
are indistinguishable there; the event's stored form keeps the constant"
[fn: build/coordinator/fn2/DSL-METATHEORY.md:503, 513-520 @worktree, read
2026-10-29]. Its authors state the limit in the same section: "It checks
submitted spelling and the common cases. A literal reached through a helper
or an unexpanded macro passes" [fn:
build/coordinator/fn2/DSL-METATHEORY.md:522 @worktree, read 2026-10-29].
None of the eight is built at `127f7b877`.

What a declaration does carry, it carries everywhere at once, which is
the reason to prefer it to a rule in a style guide: the width moved into
the generated setter's guard once, in `fn2-columns-accessor-events` [fn:
fn2/books/columns.lisp:470-539 @127f7b877], and every table declared with
`defcolumns` has it from the next certification on. The examples in
`examples/assured/` keep each rule in one generator for the same reason:
`columns.lisp` for widths, rows and init, `machine.lisp` for
continuations, `budget.lisp` for budgets, `named-stop.lisp` for stops,
and `ownership.lisp` for the theorems that ownership states exist to make
provable.
