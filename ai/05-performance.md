# ai/05. Performance: what runs, static allocation, consing, generators

Load after `ai/04-modelling.md`. The terse twin of
`humans/05-high-performance.md`. Every form is copied from a certified book
under `examples/performance/`; its numbers are in that book's `.cert.out`.
"The laptop" is ACL2 8.7 on SBCL 2.6.8, Apple M2 Max. fn coordinator files are
cited `@worktree` (read 2026-10-28). See `fn-lessons/01-octet-lists-twins.md`
and `fn-lessons/18-twin-forest.md` for the wound behind section 4.

## 0. Pitfalls

| symptom | cause | go to |
| --- | --- | --- |
| an `mbe` function allocates what its `:logic` builds | guards not verified: `*1*` runs `:logic` | 1 |
| every request walks the whole state | a whole-state recognizer in the guard of a host-called entry | 1 |
| deep recursion, one stack frame per record | an unverified function on the path runs its `*1*` recursion | 1 |
| "A single-threaded object, namely TAGTAB, is being used where an ordinary object is expected" | list view of a stobj as `:logic` of `mbe` | 1 |
| inserts get slower as the table grows | resizing an array by one slot (quadratic) | 2 |
| a guard-verified resize call certifies, then errors at run time | `:resizable nil` still defines `resize-x` | 2 |
| 16 KiB allocated per call | `with-local-stobj` per call allocates the stobj | 2 |
| a guard proof of a stobj function runs for minutes with `prove: 0.00` | the creator of a large stobj is a huge ground term | 2 |
| goal `(RATIONALP I)` in a typed loop's guard proof | the `:guard`'s own `<=` needs `(natp i)` first | 2 |
| `(ACL2-NUMBERP (NTH I (CAR ST)))` open in a guard proof | element facts as rewrite rules; need type-prescription + linear | 2 |
| timing lines missing | `time$` inside `assert-event` prints at certification only | 3 |
| a concrete representation landed, the list path still runs | a twin kept callable | 4 |

## 1. What runs when

Every function is a `*1*` executable counterpart and a raw Lisp definition; a
guard-verified `*1*` checks the guard once and "escapes to the submitted
definition" [:doc evaluation], [:doc guards-and-evaluation]. `mbe`: "only the
`:logic` code is evaluated unless the call is in the body of a guard-verified
function or under a call of a `:program` mode function; in those cases only the
`:exec` code is evaluated. This implies that equality of `:exec` and `:logic`
code is never checked at runtime"; in safe mode (`defconst`) both run; under
guard checking `:all`/`:none` only `:logic` [:doc mbe]. Measured on one
`count-evens` pair, 100,000 elements, bytes allocated by the call
[example: examples/performance/what-runs.lisp]
[measured: `examples/certify.sh performance/what-runs.lisp`, `.cert.out`; laptop]:

| caller | callee | body that ran | bytes |
| --- | --- | --- | ---: |
| guard-verified | guard-verified | raw, `:exec` | 0 |
| guard-verified, via `ec-call` | unverified | `*1*`, `:logic` | 851,760 |
| `:program` | unverified | raw, `:exec` | 0 |
| unverified (`*1*`) | guard-verified | callee checks guard, then raw `:exec` | 0 |

Rules:

- Verify the guards of every function on an executed path; an unverified one
  ran "its recursion, one control-stack frame per record or octet"
  [fn: books/store-log.lisp:102-108 @3bbfc4dca].
- The guard of the entry the host calls is evaluated on every call; never a
  whole-state recognizer there ("`fn-statep` is Theta(n^2) ... and it ran on
  every served operation") [fn: docs/proof-style.md:301-303 @3bbfc4dca],
  [fn: docs/proof-style.md:873-876 @3bbfc4dca].
- `mbt` costs nothing in raw Lisp ("macroexpands to `t`") [:doc mbt].
- Assert the property execution depends on, from the world
  [example: examples/performance/what-runs.lisp]:

  ```lisp
  (assert-event (eq (symbol-class 'count-evens (w state)) :common-lisp-compliant))
  (assert-event (eq (symbol-class 'count-evens-unverified (w state)) :ideal))
  (assert-event (eq (symbol-class 'what-runs-program (w state)) :program))
  ```

  fn's `definterface` checks a declared entry class against the world at
  admission [fn: books/definterface.lisp:13-41 @3bbfc4dca].
- Guard verification alone is not the speed: "the executable-counterpart
  executes almost as fast as the submitted definition, at least if the
  evaluation of the guards is fast"; the gains are `:exec` and trusted type
  declarations [:doc guards-and-evaluation].
- A stobj's list view lives in a theorem, not in `:logic`
  [example: examples/performance/mbe-fixnum-loop.lisp]:

  ```lisp
  (defun count-tag-st (x tagtab)
    (declare (xargs :stobjs tagtab
                    :guard (unsigned-byte-p 61 x)))
    (mbe :logic (count-tag-rec x 0 tagtab)
         :exec (count-tag-loop x 0 0 tagtab)))

  (defthm count-tag-st-is-count-tag
    (implies (tagtabp tagtab)
             (equal (count-tag-st x tagtab)
                    (count-tag x (nth *tagi* tagtab)))))
  ```

## 2. Static allocation: fixed-size stobjs

Pitfalls:

- Growing by one slot: fn's page-pointer array "resized ... by one per split,
  O(P) a split and O(P^2) in all"; worst add 114,752 bytes, fixed by a
  two-level directory that grows a page at a time
  [fn: books/msgid-linear-exec.lisp:7-24 @3bbfc4dca]. "Array resizing is
  relatively slow" [:doc defstobj].
- `:resizable nil` still defines `resize-keys`: guard-verified, the identity in
  the logic, a hard error when run ("illegal to resize this array")
  [example: examples/performance/bounded-table.lisp], [:doc defstobj].
- `with-local-stobj` expands to `(let ((st (create-st))) ...)`
  [:doc with-local-stobj]: 1,000 calls with a 2,048-word scratch stobj
  allocated 16,384,928 bytes; 1,000 steps over one threaded stobj, 51,152
  [measured: `examples/certify.sh performance/time-list-vs-stobj.lisp`,
  `.cert.out`; laptop]. Scratch space a loop needs is a field of the
  long-lived stobj or one stobj threaded through the loop.
- A guard conjecture over a large local stobj mentions its creator, a list as
  long as the array; a 1,000,000-word draft ran 119 s with `prove: 0.00` until
  `timeout` killed it [measured: the `bench-stobj` draft over the 1,000,000-word
`vec` of examples/performance/time-list-vs-stobj.lisp, piped into the laptop
REPL under `timeout 120` and again under `timeout 240`].
  Prove the recognizer of the creator and disable the creator right after the
  `defstobj` [example: examples/performance/time-list-vs-stobj.lisp]:

  ```lisp
  (defthm vecp-of-create-vec (vecp (create-vec)))
  (in-theory (disable create-vec))
  ```

- The guard proof of a typed loop needs (1) element facts as
  `:type-prescription` and `:linear` rules (a rewrite rule concluding
  `unsigned-byte-p` left `(ACL2-NUMBERP (NTH I (CAR TAGTAB)))` open) and (2)
  `(natp i) (natp acc)` leading the `:guard` (else `(RATIONALP I)`); the book
  keeps both refused drafts as `local` `must-fail`s
  [example: examples/performance/mbe-fixnum-loop.lisp]:

  ```lisp
  (defthm tagp-nth-natp
    (implies (and (tagp l) (natp i) (< i (len l)))
             (natp (nth i l)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable nth))))

  (defthm tagp-nth-below
    (implies (and (tagp l) (natp i) (< i (len l)))
             (< (nth i l) (expt 2 61)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nth))))
  ```

  Each array also needs an update lemma (`keysp-of-update-nth`)
  [example: examples/performance/bounded-table.lisp],
  [fn: books/msgid-linear-exec.lisp:146-153 @3bbfc4dca].

Mechanism: `(ARRAY type-spec (max))`, `max` a natural or a defined constant;
updated in place [:doc defstobj]. Options:

- `:inline t`: accessors as macros; "a factor of 10 or more" on contrived
  array code, "at least 2" on realistic [:doc defstobj].
- `:non-executable t`: no global instance; for stobjs used only locally or as
  fields [:doc defstobj].
- `:non-memoizable t`: no memo-flush test on updates [:doc defstobj];
  fn's octet buffer: "one load, compare and branch per array store"
  [fn: books/octets-stobj.lisp:72-79 @3bbfc4dca].
- `:element-type t`: on a double-float array the manual measured no SBCL gain
  (reads 0.23 s with, 0.21 s without) and suggests it for read-heavy CCL code
  [:doc defstobj-element-type].

Words: `(unsigned-byte 61)` is a fixnum on SBCL x86-64, so "the accessor
returns it unboxed and the scan allocates nothing" (6,364 bytes consed per
lookup before, 16 after) [fn: books/msgid-linear-exec.lisp:26-36 @3bbfc4dca];
on the arm64 laptop a 1,000,000-word array cost 8 bytes a word to create, and
fill and 100 scans allocated nothing [measured: `time-list-vs-stobj.cert.out`;
laptop]. `type` and `the` are guard obligations and help only once guards
are verified; otherwise `THE` is a run-time check [:doc the]. No `(declare
(optimize ...))`: ACL2 does not support it [:doc declare]; inlining is
`defun-inline` (`f$inline` plus macro `f`) [:doc defun-inline],
[fn: books/msgid-linear-exec.lisp:244-263 @3bbfc4dca].

Shape: the loop, whole [example: examples/performance/mbe-fixnum-loop.lisp]:

```lisp
(defconst *slots* 1024)

(defstobj tagtab
  (tag :type (array (unsigned-byte 61) (*slots*)) :initially 0 :resizable nil)
  :inline t)

(defun count-tag-loop (x i acc tagtab)
  (declare (xargs :stobjs tagtab
                  :guard (and (natp i) (natp acc) (<= i *slots*) (<= acc i))
                  :measure (nfix (- *slots* (nfix i))))
           (type (unsigned-byte 61) x acc)
           (type (integer 0 1024) i))
  (if (mbe :logic (or (not (natp i)) (>= i *slots*)) :exec (= i *slots*))
      acc
    (count-tag-loop x
                    (the (integer 0 1024) (+ 1 i))
                    (if (= x (the (unsigned-byte 61) (tagi i tagtab)))
                        (the (unsigned-byte 61) (+ 1 acc))
                      acc)
                    tagtab)))
```

A fixed table that refuses by name when full, and says so as a theorem
[example: examples/performance/bounded-table.lisp]:

```lisp
(defun tbl-insert (k tbl)
  (declare (xargs :stobjs tbl
                  :guard (unsigned-byte-p 61 k)))
  (let ((n (used tbl)))
    (if (>= n *table-cap*)
        (mv :full tbl)
      (let* ((tbl (update-keysi n k tbl))
             (tbl (update-used (+ 1 n) tbl)))
        (mv :ok tbl)))))

(defthm tbl-insert-full-is-a-refusal-and-a-no-op
  (implies (and (tblp tbl)
                (<= *table-cap* (used tbl)))
           (and (equal (mv-nth 0 (tbl-insert k tbl)) :full)
                (equal (mv-nth 1 (tbl-insert k tbl)) tbl))))
```

## 3. Finding the consing

A list costs 16 bytes per element: 1,000,000 naturals 15,986,880 bytes; into a
stobj array 0. Sequential scans cost the same (0.23 s vs 0.26 s for 100 scans);
positional reads do not (100 reads of word 999,999: 0.10 s by `nth`, below
timer resolution by the accessor) [measured: `time-list-vs-stobj.cert.out`;
laptop]. The cost of a list is what it allocates, retains and makes linear.

Tools:

- `time$`: `(time$ form :mintime 0 :msg "...: ~sa bytes, ~st s~%")`; `~sa`
  bytes allocated, `~st` real time; thresholds filter output; usable inside
  function bodies [:doc time$]. Shape
  [example: examples/performance/what-runs.lisp]:

  ```lisp
  (time$ (count-evens l)
         :mintime 0
         :msg "verified callee from a verified caller: ~sa bytes~%")
  ```

- A test book is the record: `time$` inside a function called by
  `assert-event` prints at certification, into `.cert.out`, and not on include
  (assertions are skipped when proofs are) [:doc assert-event]
  [measured: including every examples/performance book in one REPL session
  printed no timing line; laptop].
- `(profile 'fn)`, run, `(memsum)`: per-call heap bytes ("Heap bytes allocated
  per call 1.64e+4") [:doc profile] [measured: `(profile 'scratch-per-call)`,
  `(scratch-per-call-k 1000 0)`, `(memsum)`; laptop]. `profile-all` needs a book
  uncertified on the laptop [:doc efficiency].
- `comp`: nothing to do on SBCL, which compiles automatically [:doc efficiency];
  `(comp :exec)` only for unverified code elsewhere [:doc comp].
- `hons-summary` for hash-consing and fast alists [:doc hons-summary].
- Raw Lisp `sb-ext:get-bytes-consed` is process-wide: keep other threads quiet
  [fn: host/native/owner.lisp:549-553 @3bbfc4dca].

Hot paths: "A function called once per request, arrival or contact must not
traverse a collection whose size does not depend on that request"
[fn: docs/proof-style.md:858-860 @3bbfc4dca]. fn's checker was
path-insensitive, context-insensitive, did not expand macros ("The tool's
silence is not a proof") [fn: docs/proof-style.md:896-909 @3bbfc4dca], and was
then deleted while the document still says it runs [fn: commit 9d5a3f99b, an
ancestor of @3bbfc4dca], [fn: docs/proof-style.md:861 @3bbfc4dca]. State the
bound in the logic or measure it in a test book; a rule whose checker is gone
is a comment.

## 4. One representation, no twins

fn's record: concrete representations landed, the list paths stayed; the
host's `(fnn-octet-list` calls grew from 130 to 263 after the decision against
them; a POST went through "18 whole-article representation changes, 16 under
the owner mutex" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:42-108 @worktree].
Cause: the law "a correspondence theorem to the list definition at every
boundary the host calls" "made each new buffer path a **twin** of a list path
... The list path stayed callable, and new host code kept calling it"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:136 @worktree].
A generator emitted a list-foundation generic beside the columnar one
[fn: books/def-representation.lisp:42-49 @3bbfc4dca]. Rules:

- The list is the `:logic` of an `mbe` or the abstraction of an abstract stobj,
  and nothing else; never callable from `:exec`
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:183 @worktree].
- The correspondence is proved once, at the representation, not at every
  caller [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:19 @worktree].
- A landing that adds the concrete path deletes the list path in the same
  change; count the list path's call sites as the measure
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:61,183 @worktree].

## 5. Batching and one executor loop, as modelled state

A batch living in the host is an unverified scheduler deciding durability:
"The books decide what the owner does; the host decides when, under which lock,
on which thread" [fn: build/coordinator/ANATOMY-20261009.md:27 @worktree].
Model the batch: one in flight, acknowledged only after its barrier, in order;
closes when the previous barrier returns, never on a timer; a failed barrier
makes members uncertain and fences [fn: specs/storage.md:443-455 @3bbfc4dca].
Shape: the invariant over acknowledgement and durability, proved for the step
[example: examples/performance/deterministic-simulation.lisp]:

```lisp
(defun gc-invp (s)
  (declare (xargs :guard (gc-statep s)))
  (and (prefixp (gc-acked s) (gc-durable s))
       (or (gc-fenced s) (equal (gc-acked s) (gc-durable s)))))

(defthm gc-step-preserves-invariant
  (implies (and (gc-statep s) (gc-invp s))
           (gc-invp (mv-nth 1 (gc-step ev s))))
  :hints (("Goal" :in-theory (disable prefixp-when-equal-lengths))))
```

One executor: "The owner machine has exactly one executing thread. I/O workers
execute actions and return completions as events; they never drive the
machine" [fn: build/coordinator/RUNTIME-MODEL-DRAFT-20261009.md:10 @worktree].
Write the layer once over a constrained machine and instantiate
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca]; it owns slots, a buffer
pool with named ownership states, outstanding uses, a borrowed read-only view,
a per-step work budget, and one commit point (`(:fsync (:done n))` of the
instance's own fsync) [fn: books/runtime-contract.lisp:17-111 @3bbfc4dca].
TigerBeetle's form: single-threaded, every in-flight operation a statically
allocated struct [paper: tigerbeetle2026-architecture.md, "Single Thread",
"Static Memory Allocation"].

## 6. TigerStyle, translated

| TigerStyle [paper: tigerbeetle2026-tiger-style.md, "Safety"] | ACL2 |
| --- | --- |
| assertions on in production | a verified guard is an assertion proved at every internal call; check only the boundary, refuse by name, guard everything behind it [:doc guards-and-evaluation] [example: examples/performance/limits-as-guards.lisp] |
| other assertion forms | `mbt` (erased by proof) [:doc mbt]; `assert$` (run-time + obligation), `assert*` (obligation only) [:doc assert$]; `assert-event` at certification [:doc assert-event] |
| a limit on everything | measure for termination; the bound a `defconst` in guards and theorems |
| assert relations of constants | `assert-event` over `defconst`s |
| explicitly sized types | `(unsigned-byte 32)` in `type`/`the`; on SBCL choose fixnum widths (61) [fn: books/msgid-linear-exec.lisp:26-31 @3bbfc4dca] |
| static allocation at startup | stobjs created once, never resized, inserts refused when full; claim "0 bytes per operation" measured in a test book |
| positive and negative space | a keystone's witness and violating values (`ai/04-modelling.md` section 16) |
| deterministic simulation | a seeded event generator over the step function, invariant checked every step, mutant caught at a constant |
| run at your own pace, batch | one executor over completions; batch closes on the barrier (section 5) |
| no recursion | every recursion has a measure, a bound in its guard, an accumulator `:exec`; unverified recursion runs as recursion |
| 70 lines per function | no measured ACL2 counterpart; fn splits books over 800 lines [fn: docs/proof-style.md:411 @3bbfc4dca] |

Limits as one table read by a macro, so the admitted term is the number
[example: examples/performance/limits-as-guards.lisp],
[fn: books/protocol-table.lisp:300-302 @3bbfc4dca]:

```lisp
(defconst *line-octets-max* 512)
(defconst *batch-records-max* 64)
(defconst *batch-octets-max* (* *batch-records-max* *line-octets-max*))

(defconst *limits*
  `((:line-octets   . ,*line-octets-max*)
    (:batch-records . ,*batch-records-max*)
    (:batch-octets  . ,*batch-octets-max*)))

(assert-event (equal *batch-octets-max* (* *batch-records-max* *line-octets-max*)))
(assert-event (< *batch-octets-max* (expt 2 60)))

(defmacro limit (name)
  (let ((pair (assoc-eq name *limits*)))
    (if (consp pair)
        (cdr pair)
      (er hard 'limit "No limit named ~x0 in *limits*." name))))

(defthm admit-batch-answer-is-within-the-ceiling
  (<= (mv-nth 1 (admit-batch l)) (limit :batch-octets))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance batch-octets-spec-bound
                                   (max (limit :line-octets)))))))
```

Deterministic simulation in a test book; the mutant step (acknowledges at the
seal, before the barrier) is caught at a replayable constant
[example: examples/performance/deterministic-simulation.lisp]:

```lisp
(defun run-check (events s i mutantp)
  (declare (xargs :guard (and (gc-statep s) (natp i))
                  :measure (len events)))
  (cond ((atom events) :ok)
        (t (mv-let (word s2)
             (if mutantp (gc-step-mutant (car events) s) (gc-step (car events) s))
             (declare (ignore word))
             (if (and (gc-statep s2) (gc-invp s2))
                 (run-check (cdr events) s2 (+ 1 i) mutantp)
               (list :violated-at i (car events)))))))

(assert-event (eq (all-seeds-ok 50 2000 nil) :ok))

(assert-event (equal (all-seeds-ok 50 2000 t)
                     '(:seed 50 (:violated-at 28 (:seal)))))
```

Mutate one side at a reachable state; a mutation visible only at an
unreachable version proves nothing
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:17 @worktree].

## 7. Code generation

"executable ACL2 code can run efficiently as Lisp" may make generation
unnecessary [paper: coglio2022-acl2-atc-proof-generating-c-code-generator.txt, section 1].
ATC and APT are not certified on the laptop; cite their tests.

- ATC targets: "in logic mode and guard-verified"; singly recursive, `o<`,
  natural measure; each formal's guard has exactly one C-type conjunct
  (`(c::uintp x)`, `(c::ucharp x)`, ...) [books: kestrel/c/atc/doc.lisp:316-420].
  `(unsigned-byte 32)` guards are not ATC input; the body uses C operations
  (`c::add-uint-uint`) [books: kestrel/c/atc/tests/checksum.lisp:93-116].
  Generated: `*program*`, `*program*-well-formed`, per-function
  `*program*-fn-correct`; valid only for non-overlapping pointer arguments
  [books: kestrel/c/atc/doc.lisp:1536-1572].
- APT: transformations with equivalence theorems; `isodata` changes a
  representation in one event, `tailrec` makes a loop, `parteval`,
  `finite-difference`, `casesplit`, `expdata`, `lift-iso`
  [books: kestrel/apt/doc.lisp:68-85], [books: kestrel/apt/isodata-doc.lisp:47-55],
  [paper: coglio2020-acl2-apt-isomorphic-data-type-transformations.txt].
  Route: spec, APT chain, ATC subset, C with its theorem
  [paper: coglio2022-acl2-atc-proof-generating-c-code-generator.txt, section 1].
- fn instead extracted translated definitions to bare SBCL (84 MB image vs
  244 MB ACL2 host core); faithfulness is a test argument, not a theorem
  [fn: build/coordinator/lanedumps/extract-forms.md:11-36 @3bbfc4dca],
  [fn: build/coordinator/ANATOMY-20261009.md:67 @worktree].

## 8. Generating macros: buy and cost

Bought: records, loops, transitions, protocol tables and interfaces as one
form each; one induction per loop shape instead of 850
[fn: docs/proof-style.md:10-17 @3bbfc4dca], [fn: books/def-loop.lisp:5-21 @3bbfc4dca].
Costs, each a rule:

- A static tool cannot see through a macro; a Python mirror of the expansion is
  a second implementation [fn: docs/proof-style.md:142-146 @3bbfc4dca]. Record
  each instance in a world table and have tools read the world
  [fn: books/def-loop.lisp:60-64 @3bbfc4dca].
- A generator low in the include graph recertifies everything above it
  (`books/defrecord.lisp`: 1192 of 1370 dependents); batch its changes
  [fn: docs/proof-style.md:147-149,459-462 @3bbfc4dca].
- Options accrete; a generator does not delete what it replaces
  [fn: books/def-loop.lisp:69-128 @3bbfc4dca].
- Generalize from the first two working instances, never as a prerequisite
  [fn: build/coordinator/RUNTIME-MODEL-DRAFT-20261009.md:39 @worktree].
