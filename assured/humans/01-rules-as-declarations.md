# 1. TigerStyle's rules as declarations

Put each rule in the declaration that generates the code it governs. A
column declaration can generate a width guard for every setter; a machine
declaration can generate its state enum, budget and dispatch. This makes the
rule reusable and gives ACL2 concrete obligations to check. It works only
for the properties the generator actually encodes. [^s1] [^s2]

[Part 1, section
5.7](../../humans/05-high-performance.md#57-tigerstyle-in-acl2) explains the
individual mechanisms: a guard is a precondition proved at each
guard-verified call site, a bound is a `defconst` used by guards and
theorems, and a fixed-size stobj supplies statically sized storage. This
chapter shows how declarations keep those rules consistent across a code
base written by many authors, including agents.

In fn2, `defcolumns` declares a table and generates its stobj, guarded
readers and setters, and shape theorems. `defmachine` adds machine states,
budgets and dispatch. A caller that cannot establish a generated guard fails
guard verification. The design aims to use those same machine and column
declarations for three outputs:

1. The ACL2 stobj implementation.
2. A flat representation and dispatcher compatible with ATC, ACL2's C
   generation tool.
3. Correspondence obligations between the two representations.

At the implementation pin used here, the first exists; the second and third
remain owed. [Chapter 7](07-honest-costs.md) accounts for that gap. [^s3]

The examples under `examples/assured/` demonstrate the techniques without
depending on fn2. Source excerpts from fn2 retain their paths and revision
pins so the implemented forms can be distinguished from proposed repairs.

## 1.1 What goes wrong: rules as conventions

The 2026-10-28 review of fn2's layer A identified three architectural
problems. The first two show how a convention can fail even when the books
certify [^s4]:

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
value))`": "A counter that overflows its column is not refused, not clamped,
not reported: the write simply does not happen" (finding A3). Readers
"return 0 for an out-of-range slot (0 = `:accept`, phase 0 = `:free`) ... A
zero is a valid value in every one of these columns" (A9). `4294967295` as
"none" "appears about 80 times across 15 files" (A11). Enum consumers type
their counts by hand, "`(< kind 14)`, `(< evkind 12)` ... Add an event kind
and every one of these silently becomes wrong" (A13) [^s5].

None of these is an ACL2 error. Every one of those books certified. A guard
is only as strong as what it says, and a convention ("callers check the
width first") is not in any guard. The remedy the review gives for A3 is the
shape of this whole chapter: "Put the width in the setter's guard so a
caller that cannot prove it fits fails guard verification; the run-time `if`
goes" [^s6].

## 1.2 Bounds in guards and in types

**The rule.** "Put a limit on everything ... all loops and all queues must
have a fixed upper bound" and "Use explicitly-sized types like `u32` for
everything" [^s7].

**How fn2 declares it.** A `defcolumns` column has a kind, `:u8`, `:u16`,
`:u32`, `:u60`, `:u64`, `:bool` or `(:enum NAME (keywords))`, and the table
has a `:rows-bound` [^s8]. After the review, the generated setter's guard
carries the width:

```lisp
(defun ,write (i v ,name)
  (declare (xargs :stobjs ,name
                  :guard (and ,guard (unsigned-byte-p ,width v))
                  :guard-hints (("Goal" :in-theory (disable ,wfp)))))
  (,raw-write i v ,name))
```

The generated row guard is `(and (natp i) (,wfp ,name) (< i (,rows
,name)))`. Guard-verified callers of either reader or setter must establish
that the row exists. [^s9] [^s10] Each column has its own width: fn2 has
"**no fixed word** ... Arithmetic above `2^62` allocates in SBCL, so hot
counters default to `:u60`; a `:u64` column on a served path must record a
`:why` explaining its width", and the macro refuses a `:u64` column without
one [^s11]. A counter that could wrap gets an incarnation column beside it:
"a counter at its limit retires and the incarnation advances, never wrapping
into a previous identity" [^s12].

**The shape to copy.** `examples/assured/columns.lisp` is a standalone
version: `(defcols NAME ((FIELD KIND) ...) :rows-bound B)` emits a stobj
with one resizable typed array per column, a `ROWS` scalar whose stobj type
is `(integer 0 B-1)`, a reader with the row guard and a setter with the
width guard [^s13]. A caller that has not established the width cannot be
guard-verified:

```lisp
(must-fail
 (defun slots-record-len-unchecked (i n slots)
   (declare (xargs :stobjs slots
                   :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                               (natp n))))
   (slots-set-len i n slots)))
```

The failed guard conjecture's checkpoint is the width itself, `(< N
4294967296)` [^s14]. The caller that certifies refuses by name at the
boundary, where the value came from:

```lisp
(defun slots-record-len (i n slots)
  (declare (xargs :stobjs slots
                  :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots)))))
  (if (unsigned-byte-p 32 n)
      (let ((slots (slots-set-len i n slots))) (mv :ok slots))
    (mv :too-long slots)))
```

The boundary checks the value once and returns a named refusal that the
caller must handle. The earlier absorbing setter silently dropped the write
on each invalid call. [^s13]

**Enums carry their count.** Finding A13's remedy is "`defcolumns` emits
`*NAME-COUNT*` per enum and the enum setter's guard is `(< v *NAME-COUNT*)`"
[^s15]. fn2's generator at `127f7b877` emits one constant per keyword and
the two conversion functions, but no count constant, and its enum setters
still guard by the byte width only [^s16]. The example emits
`*slot-phase-count*` and uses it in the setter's guard [^s13]:

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
relationships of compile-time constants as a sanity check" [^s17] is
`assert-event` over `defconst`s; part 1 shows the form
(`humans/05-high-performance.md` section 5.7, [^s18]).

## 1.3 Budgets as guards and measures

**The rule.** "all loops and all queues must have a fixed upper bound to
prevent infinite loops or tail latency spikes ... Where a loop cannot
terminate (e.g. an event loop), this must be asserted" [^s19].

**The execution contract.** EXECUTION-MODEL rule 3, "Bounded everything,
simultaneously": "Every machine run has a work cap (initially 4 KiB
parsed/rendered/hashed, 32 structural steps, 4 action descriptors ...),
every turn has `H = 128` observations, `K = 64` calendar visits, `Aturn =
256` descriptors; every queue has a capacity with a named exhaustion
behaviour that is an ordinary continuation, never a crash ... Budget
exhaustion leaves a resumable continuation" [^s20].

**How fn2 declares it.** Each machine kind declares `:budget (:bytes 4096
:steps 32 :descriptors 4)` [^s21], and `defmachine` emits a constant and a
charge function that refuses before any mutation:

```lisp
(defun ,charge (bytes steps descriptors)
  (declare (xargs :guard (and (natp bytes) (natp steps) (natp descriptors))))
  (if (and (<= bytes ,bytes) (<= steps ,steps) (<= descriptors ,descriptors))
      (mv bytes steps descriptors)
    (mv nil nil nil)))
```

with the comment "Preflight and finish use the same simultaneous caps. A
refused preflight yields before mutation" [^s22].

**The shape to copy.** In ACL2 a budget does three jobs at once, and the
example gives each its form [^s23]:

- **The measure.** The run loop's measure is the remaining step budget,
  not the queue's length, so termination is proved from the budget and a
  run is bounded even when the queue is not. This excerpt shows the
  signature and measure; the example book contains the full function:
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

The execution design's statement, "the caps are loop bounds; a cost
certificate per run makes them a CPU bound" [^s20] names the limit of this:
the theorem bounds what the budget counts. It does not bound what the budget
does not count, and fn2's review found the step costs in its machines
"self-declared" constants (`24`, `8`, `1`) typed at each use, and its owed
refinement's work bound "self-declared constants (`24`, `4129`)" [^s24]. A
charge is only as honest as the count it charges; fn2's WORK accounting
checker recomputes work from emitted records for that reason (chapter 2).

## 1.4 No allocation after init

**The rule.** "All memory must be statically allocated at startup. **No
memory may be dynamically allocated (or freed and reallocated) after
initialization.**" [^s25].

**How fn2 declares it.** The `defcolumns` header comment: "Generated array
storage is the executable representation. The row/table views are
non-executable, and resizing belongs only to the generated init" [^s26]. The
generated `NAME-INIT` is the one function that calls the `RESIZE-` updaters
[^s27]; every generated setter comes with a `-PRESERVES-WFP` theorem, and
`NAME-WFP` says every column's length equals the row count, so no setter can
change a length [^s28]. The pool carves its slots once: "At init the profile
names size classes `((count . bytes) ...)`; the pool resizes its byte array
to the sum and its slot table to the total count ... No allocation after
init; no fragmentation; a class with no free slot answers `:exhausted`,
which the caller holds as a continuation" [^s29].

**What "init" may size.** Ember's ruling is "No compile-time ceilings": data
limits are the operator profile's, and "structural capacities bound active
execution state only" [^s30]. So init reads a profile and sizes from it. The
review found the inverse sin, profile fields that are not configurable:
"`fn2-machines-profilep` requires `run-bytes = 4096`, `run-steps = 32`,
`run-descriptors = 4`; the trace capacity is `4*(H+K)` hard-coded in
`fn2-core-init`. A profile that pretends to configure what the code fixes
misleads every operator who reads it" (A28) [^s31].

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

This theorem establishes the logical half of the rule. [^s13] The run-time
half, that nothing else conses on the served path, is a measurement, per
operation, and part 1 gives its form ("0 bytes" over a named operation under
`time$`, `humans/05-high-performance.md` section 5.3).

## 1.5 Ownership states

**What goes wrong.** A buffer handed to the host for a send can be freed and
reused while the host still reads it; a stale handle from before a reuse can
write into the new owner's bytes. EXECUTION-MODEL rule 6: "Receives and
reads lend a writable range the core cannot inspect until completion returns
it; sends and writes lend immutable bytes whose reuse waits for every
external borrow to end (zero-copy send progress is not release)" [^s32].

**How fn2 declares it.** The ownership state is a declared enum column, with
a generation beside it. This excerpt shows those columns:

```lisp
(defcolumns fn2-pool
  ((gen :u60) (base :u60) (cap :u32)
   (state (:enum fn2-pool-state (:free :workspace :leased-in :leased-out :handed :retired)))
   ...
```

The declaration pairs each ownership state with its generation. [^s33] A
handle is "`(slot, generation, offset, length)`" [^s32], and the generation
check comes first: `((not (equal gen (fn2-pool-gen slot fn2-pool))) :stale)`
[^s34]. The ownership rules are recorded as **owed** statements: conjectures
whose proofs remain outstanding. Their **teeth** are executable witnesses
and negative controls that test whether a statement distinguishes intended
behavior from a selected defect. The recorded rules are: "Every
handle-taking export refuses a mismatched generation before other decisions
and preserves the identical logical pool" (`FN2-POOL-STALE`); "Across every
pool operation, a borrowed slot cannot become free or retired, change
generation, or have any backing byte changed" (`FN2-POOL-NO-REUSE`); "Every
operation preserves monotone generations and retirement"
(`FN2-POOL-GENERATION`) [^s35]. The teeth pass, but these production
obligations remain unproved (chapter 7).

**Where fn2's declaration is still weaker than the rule.** The review found
a borrow tracked as a count without its holder: "Typed edges are counters
without holders ... any caller holding the extent's `(epoch, counter)` can
drop another machine's `:borrow` or `:promised-read` and make the extent
releasable under a live reader. This is the pool's `release-out` defect ...
repeated on the durability path" (B10) [^s36]. An ownership state is a claim
about who owns; a count says only how many.

**The shape to copy.** `examples/assured/ownership.lisp` declares the states
as a `defcols` enum (free, leased, borrowed, retired) and proves the three
rules for its small pool: `slot-free-stale` and `slot-borrow-stale` (a stale
handle is refused and nothing changes), `slot-free-refuses-borrowed` (no
reuse while borrowed), `slot-free-generation-monotone` and
`slot-free-ok-invalidates-handle` (a successful free bumps the generation,
so every old handle is stale) [^s37]. Its teeth run the whole story:

```lisp
(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

lease, borrow, a free refused while borrowed, return, a free that bumps the
generation to 1, and the old handle refused as stale.

## 1.6 Assert, never absorb: named stops

**What goes wrong.** The review's first finding: "`fn2-core-issue` reserves,
leases, then calls `fn2-op-set-range`, `-set-capability`, `-set-storage`,
`-set-cancel-target` and `fn2-op-enqueue` binding every result code to
`?ignored`, and returns `:ok`. If `enqueue` ever refuses ... the caller is
told the op was issued, the row stays `reserved` holding a credit, and the
pool lease is outstanding forever" (A1) [^s38].

**The rule.** "Assertions detect programmer errors. Unlike operating errors,
which are expected and which must be handled, assertion failures are
unexpected. The only correct way to handle corrupt code is to crash" [^s39].

**Three shapes.** `examples/assured/named-stop.lisp` writes one `issue`
operation three ways over a core whose invariant is `free + queued = cap` [^s40]:

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
non-`:ok` into a stop with evidence" [^s38]. fn2 took shape 3 for `fn2-core-issue`: each post-reservation
call now maps a refusal to its own stop reason (`*fn2-stop-reason-issue-range*`,
`-capability`, `-storage`, `-cancel-target`, `-enqueue`) and the core stops
with it [^s41]; `fn2-core-stop` keeps
the first reason ("First corruption wins: later cleanup cannot erase the
diagnostic") [^s42]; the reasons are
a declared enum of twenty-one keywords in the executor's control table [^s43]. Shape 3 is the honest interim:
it makes the impossible visible to the simulator, which asserts on stop
reasons (chapter 2), but each stop branch is still code that the
invariant says cannot run, and the proof that would delete it is owed.

**Where the boundary is.** The review's remedy for sin 1 is "architectural,
not local: name the boundary (host-supplied observations and descriptors
...), validate there only, and inside the core let guards and `mbt` carry
the invariants, with any residual impossibility stopping the executor with a
reason the simulator asserts on" [^s44]. `fn2-core-issue` still validates every scalar width at run
time on entry [^s45], which is right
only if it is the boundary.

**A refusal is not always corruption.** Running out is expected:
`reserve` answering `:exhausted` is a continuation the caller holds
(EXECUTION-MODEL rule 3), and the example keeps it as a plain refusal [^s40]. fn2 still has the third kind,
a non-exhaustion refusal in a machine, marked "TODO
R6-NONEXHAUSTION-REFUSAL: replace this retained stop with the named
close/release or evidence posture chosen by R6" [^s46].

## 1.7 `defcolumns` and `defmachine` as the worked forms

**What `defcolumns` emits.** In one `encapsulate`: the enum constants and
code/keyword functions; the `defstobj` with one array per column and the
`ROWS` scalar; per-array type facts by functional instance of one list
template ("One list template; each column instantiates it, without
repeating induction"); the record and shape facts; `NAME-WFP`; `NAME-INIT`
and its theorems; per column a reader and a setter with their type,
bound, `-PRESERVES-WFP`, `-PRESERVES-TYPE` and `-ROWS` theorems; the
non-executable row and table views; and a row in the world table
`fn2-columns` recording the declaration [^s47]. Chapter 4 explains the generic template and the measurements used to
check how certification cost grows with field count.

**What `defmachine` emits.** A machine is `defcolumns` plus: a `phase`
column of the machine's state enum, the common fields (generation,
principal, account, ready links, wait reason, deadline), the `-PUT` and
`-PUT-CORE` macros, the budget constant and charge function, the
generated `NAME-OBSERVES-P`, the row initializer, and a row in
`fn2-machine-kinds` [^s48]. Its declarations are short: [^s49]

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

**Continuations name functions.** Before the repair, "`defmachine` is a
template engine, not a declaration. `:continuations` and `:initial` are
code fragments pasted into generated bodies and they reference the
generator's private binding names" (A23) [^s50]. Now each continuation is a symbol, and an initial value is a
constant or a named function of `(slot base n gen)` [^s51]. `examples/assured/machine.lisp` makes the check explicit: its
`defmach` is a `make-event` that reads the world and refuses the
declaration unless every state has one continuation and every continuation
is an existing guard-verified function of `(steps st)`; the book refuses a
pasted form, a continuation not yet defined, and a state without a
continuation, each by `must-fail` and each for the declared reason [^s52]. The dispatch the macro emits refuses an unknown phase by name
(`:bad-phase`), never by a default arm that runs something.

**Obligations that nothing states.** The review: "The table row records
`:obligations (initialization preservation frame output-correspondence
budget-progress flat-representation flat-transition)` and generates none
of them" (A23). At `127f7b877` the list is still there, but each entry must
be `:owed` or name a registered owed row or generator, checked by the
`make-event` in `defmachine`, which refuses "Unregistered or unstated
machine obligation" [^s53]. A name is not a statement; DSL-METATHEORY's plan replaces the
list with an obligation store whose rows carry their statements (chapter
6, chapter 7).

**What the forms still do not emit.** The review's A17: four copies of a
put-binding generator, "about seventeen 'preserves type/wfp/rows' macros",
four snapshot/copy/diff generators, all hand-written beside the DSL [^s54]. `fn2-core-shape-lemmas` is one of them [^s55]. The sentinel `4294967295` is still
spelled out in the listener's admission [^s56]. Move derivable consumer code into the declaration generator so the
consumer does not have to maintain another copy of the same rule.

## 1.8 Check the code that declarations do not generate

A generator checks what it is given. It cannot see a literal compared with
an enum in a consumer it did not generate, a field read by position, or a
specification function called on a served path. fn2's metatheory plan adds
eight expansion-time and assembly-time guards for exactly those sins (an
enum compared as an integer, positional access, a specification on a
served path, the absorbed refusal and the lying read among them), reading
submitted forms rather than translated bodies, because "A translated body
inlines a constant's value, so an enum comparison and a literal comparison
are indistinguishable there; the event's stored form keeps the constant" [^s57]. Its authors state the limit in the same section: "It checks
submitted spelling and the common cases. A literal reached through a helper
or an unexpanded macro passes" [^s58].
None of the eight is built at `127f7b877`.

What a declaration does carry, it carries everywhere at once, which is
the reason to prefer it to a rule in a style guide: the width moved into
the generated setter's guard once, in `fn2-columns-accessor-events` [^s1], and every table declared with
`defcolumns` has it from the next certification on. The examples in
`examples/assured/` keep each rule in one generator for the same reason:
`columns.lisp` for widths, rows and init, `machine.lisp` for
continuations, `budget.lisp` for budgets, `named-stop.lisp` for stops,
and `ownership.lisp` for the theorems that ownership states exist to make
provable.

[Part 3 contents](../README.md) | [Next chapter](02-simulation-and-checkers.md)

[^s1]: [fn: fn2/books/columns.lisp:470-539 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L470).

[^s2]: [fn: fn2/books/machines.lisp:203-241 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L203).

[^s3]: [fn: fn2/docs/design/EXECUTION-MODEL.md:30 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/design/EXECUTION-MODEL.md#L30).

[^s4]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:185-187 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L185).

[^s5]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:26, 32, 39, 41 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L26).

[^s6]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:26 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L26).

[^s7]: [paper: tigerbeetle2026-tiger-style.md, lines 96-102]

[^s8]: [fn: fn2/books/columns.lisp:629-636, 656-673 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L629).

[^s9]: [fn: fn2/books/columns.lisp:488-492 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L488).

[^s10]: [fn: fn2/books/columns.lisp:482-487 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L482).

[^s11]: [fn: fn2/docs/a-pool-host-sim.md:34-41 @127f7b877; fn: fn2/books/columns.lisp:671-672 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L34).

[^s12]: [fn: fn2/docs/a-pool-host-sim.md:48-50 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L48).

[^s13]: [example: examples/assured/columns.lisp] [Source](../../examples/assured/columns.lisp).

[^s14]: [measured: REPL `(include-book "columns")` then the form above without `must-fail`, ACL2 8.7, laptop, 2026-10-29]

[^s15]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:41 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L41).

[^s16]: [fn: fn2/books/columns.lisp:87-117, 481, 490 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L87).

[^s17]: [paper: tigerbeetle2026-tiger-style.md, line 128]

[^s18]: [example: examples/performance/limits-as-guards.lisp] [Source](../../examples/performance/limits-as-guards.lisp).

[^s19]: [paper: tigerbeetle2026-tiger-style.md, lines 96-100]

[^s20]: [fn: fn2/docs/design/EXECUTION-MODEL.md:17 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/design/EXECUTION-MODEL.md#L17).

[^s21]: [fn: fn2/books/machines-a.lisp:21, 34, 51 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a.lisp#L21).

[^s22]: [fn: fn2/books/machines.lisp:218-226 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L218).

[^s23]: [example: examples/assured/budget.lisp] [Source](../../examples/assured/budget.lisp).

[^s24]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:43, 87 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L43).

[^s25]: [paper: tigerbeetle2026-tiger-style.md, lines 151-152]

[^s26]: [fn: fn2/books/columns.lisp:1-3 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L1).

[^s27]: [fn: fn2/books/columns.lisp:590-594 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L590).

[^s28]: [fn: fn2/books/columns.lisp:523-526, 577-580 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L523).

[^s29]: [fn: fn2/docs/a-pool-host-sim.md:56-59 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L56).

[^s30]: [fn: fn2/docs/design/EXECUTION-MODEL.md:40 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/design/EXECUTION-MODEL.md#L40).

[^s31]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:66 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L66).

[^s32]: [fn: fn2/docs/design/EXECUTION-MODEL.md:20 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/design/EXECUTION-MODEL.md#L20).

[^s33]: [fn: fn2/books/pool.lisp:8-10 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/pool.lisp#L8).

[^s34]: [fn: fn2/books/pool.lisp:49 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/pool.lisp#L49).

[^s35]: [fn: fn2/docs/OWED.md:12-16 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L12).

[^s36]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:119 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L119).

[^s37]: [example: examples/assured/ownership.lisp] [Source](../../examples/assured/ownership.lisp).

[^s38]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:24 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L24).

[^s39]: [paper: tigerbeetle2026-tiger-style.md, lines 103-106]

[^s40]: [example: examples/assured/named-stop.lisp] [Source](../../examples/assured/named-stop.lisp).

[^s41]: [fn: fn2/books/core.lisp:250-267 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/core.lisp#L250).

[^s42]: [fn: fn2/books/core.lisp:133-147 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/core.lisp#L133).

[^s43]: [fn: fn2/books/exec-state.lisp:6-15 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/exec-state.lisp#L6).

[^s44]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:185 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L185).

[^s45]: [fn: fn2/books/core.lisp:233-238 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/core.lisp#L233).

[^s46]: [fn: fn2/books/machines-a-run.lisp:75-78 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a-run.lisp#L75).

[^s47]: [fn: fn2/books/columns.lisp:17-32, 564-622 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L17).

[^s48]: [fn: fn2/books/machines.lisp:6-8, 203-241 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L6).

[^s49]: [fn: fn2/books/machines-a.lisp:17-26 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a.lisp#L17).

[^s50]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:61 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L61).

[^s51]: [fn: fn2/books/machines.lisp:32-39 @127f7b877; fn: fn2/books/machines-a.lisp:11-15 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L32).

[^s52]: [example: examples/assured/machine.lisp; measured: REPL of the three refused forms after `(include-book "machine")`, ACL2 8.7, laptop, 2026-10-29]

[^s53]: [fn: fn2/books/machines.lisp:174-192, 261-267 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L174).

[^s54]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:50 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L50).

[^s55]: [fn: fn2/books/core.lisp:122-131 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/core.lisp#L122).

[^s56]: [fn: fn2/books/machines-a-run.lisp:86 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a-run.lisp#L86).

[^s57]: [fn: fn2/docs/design/DSL-METATHEORY.md:503, 513-520 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L503).

[^s58]: [fn: fn2/docs/design/DSL-METATHEORY.md:522 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L522).
