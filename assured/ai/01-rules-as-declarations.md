# assured/ai/01. TigerStyle's rules as declarations

Load when generating storage, bounds, budgets, ownership transitions or
machine dispatch. Terse twin of `assured/humans/01-rules-as-declarations.md`.
Use the forms in their cited example book's context. fn2 citations are
pinned to `127f7b877`; coordinator citations retain the humans chapter's
`@worktree` read date, 2026-10-29.

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| oversized write disappears; invalid read returns valid-looking zero | checks absorb errors inside accessors [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:26, 32, 39, 41 @worktree, read 2026-10-29] | 1 |
| enum grows but consumers retain old bounds | handwritten counts [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:41 @worktree, read 2026-10-29] | 1 |
| work step fails guard verification | caller lacks the budget fact [example: examples/assured/budget.lisp] | 2 |
| profile advertises configuration that code fixes | hard-coded capacities [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:66 @worktree, read 2026-10-29] | 3 |
| old handle reaches reused storage | generation check missing; prove stale refusal [example: examples/assured/ownership.lisp] | 4 |
| issue answers `:ok` but spends credit without enqueueing | absorbed refusal [example: examples/assured/named-stop.lisp] | 5 |
| continuation depends on generator-private bindings | pasted code instead of function names [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:61 @worktree, read 2026-10-29] | 6 |
| declaration exists but consumer still uses literals | generator does not inspect that consumer [fn: build/coordinator/fn2/DSL-METATHEORY.md:503, 513-520 @worktree, read 2026-10-29] | 7 |

## 1. Put widths, row bounds and enum counts in the declaration

- Replace silent setter refusal with a width guard. Require a valid row in
  both reader and setter guards. fn2's repair puts the width in the setter
  [fn: fn2/books/columns.lisp:488-492 @127f7b877]; its row guard requires
  a natural index below `ROWS` and `WFP`
  [fn: fn2/books/columns.lisp:482-487 @127f7b877].
- Generate enum constants and their count. The example guards enum writes
  with the count; fn2 still guards them by byte width and emits no count
  constant [example: examples/assured/columns.lisp]
  [fn: fn2/books/columns.lisp:87-117, 481, 490 @127f7b877].

```lisp
(defcols slots
  ((phase (:enum slot-phase (:free :leased :borrowed :retired)))
   (gen :u60)
   (len :u32))
  :rows-bound 1024)

(assert-event (equal *slot-phase-count* 4))
(assert-event (equal *slot-phase-borrowed* 2))
```

[example: examples/assured/columns.lisp].

- Reject the caller that proves only `natp`, without the column width
  [example: examples/assured/columns.lisp]:

```lisp
(must-fail
 (defun slots-record-len-unchecked (i n slots)
   (declare (xargs :stobjs slots
                   :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                               (natp n))))
   (slots-set-len i n slots)))
```

- Read the failed guard checkpoint as the missing fact: `(< N 4294967296)`
  [measured: REPL `(include-book "columns")` then the form
above without `must-fail`, ACL2 8.7, laptop, 2026-10-29].
- Validate at the boundary; return a named refusal there
  [example: examples/assured/columns.lisp]:

```lisp
(defun slots-record-len (i n slots)
  (declare (xargs :stobjs slots
                  :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots)))))
  (if (unsigned-byte-p 32 n)
      (let ((slots (slots-set-len i n slots))) (mv :ok slots))
    (mv :too-long slots)))
```

- Assert relationships between constants with `assert-event` over
  `defconst`s [example: examples/performance/limits-as-guards.lisp].

## 2. Make the budget a measure, a guard and a theorem

- Do not let queue length determine one run's work. Measure the run by
  remaining steps; preflight before spending; leave an item queued when
  it does not fit [example: examples/assured/budget.lisp].

```lisp
(defun machine-run (queue bytes steps done)
  (declare (xargs :guard (and (itemsp queue) (natp bytes) (natp steps) (natp done))
                  :measure (nfix steps)))
  (if (or (atom queue) (zp steps))
      (mv :idle queue bytes steps done)
    (mv-let (okp bytes2 steps2) (run-charge bytes steps (car queue))
      (declare (ignore bytes2))
      (if (not okp)
          (mv :yield queue bytes steps done)
        (mv-let (bytes3 done3) (copy-item (car queue) bytes done)
          (machine-run (cdr queue) bytes3 steps2 done3))))))

(assert-event
 (equal (mv-list 5 (machine-run '(4000 200 10) *run-bytes* *run-steps* 0))
        '(:yield (200 10) 96 31 4000)))
```

[example: examples/assured/budget.lisp].

- Put `(<= want bytes)` in the work step's guard. Prove
  `one-run-within-caps`, `machine-run-spends-what-it-charges` and
  `machine-run-yield-keeps-head` [example: examples/assured/budget.lisp].
- Do not call self-declared charges a CPU bound. fn2's review found
  step costs and refinement bounds typed as constants at their uses
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:43, 87 @worktree, read 2026-10-29].

## 3. Size at init; preserve shape through setters

- Do not present fixed values as operator configuration. Size from the
  profile; fn2's review found profile fields constrained to hard-coded
  values [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:66 @worktree,
read 2026-10-29].
- Keep resizing in generated init. Compose setter preservation theorems
  without reopening the table predicate [example: examples/assured/columns.lisp]:

```lisp
(defthm slots-two-writes-keep-shape
  (implies (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                (natp j) (< j (slots-rows slots)))
           (and (slots-wfp (slots-set-gen j g (slots-set-len i n slots)))
                (equal (slots-rows (slots-set-gen j g (slots-set-len i n slots)))
                       (slots-rows slots)))))
```

- Scope this result to shape preservation through these setters; it states
  `WFP` and unchanged `ROWS`, not bytes allocated by execution
  [example: examples/assured/columns.lisp].

## 4. Declare ownership states; prove stale refusal and no reuse

- Refuse stale generations before state decisions. Refuse freeing borrowed
  slots; retire at the generation limit instead of wrapping
  [example: examples/assured/ownership.lisp].
- State the unchanged-state result, not only the refusal code
  [example: examples/assured/ownership.lisp]:

```lisp
(defthm slot-free-stale
  (implies (not (equal g (slots-gen i slots)))
           (and (equal (mv-nth 0 (slot-free i g slots)) :stale)
                (equal (mv-nth 1 (slot-free i g slots)) slots))))

(defthm slot-free-refuses-borrowed
  (implies (equal (slots-phase i slots) *slot-phase-borrowed*)
           (equal (mv-nth 1 (slot-free i g slots)) slots)))

(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

- Prove generation monotonicity and successful-free invalidation:
  `slot-free-generation-monotone`, `slot-free-ok-invalidates-handle`.
  These are proved for the example; fn2's ownership obligations remain
  owed [example: examples/assured/ownership.lisp].
- Track the borrower, not only a count. fn2's review found callers able
  to drop another machine's borrow and permit release under a live reader
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:119 @worktree, read 2026-10-29].

## 5. Prove internal success or stop with a named reason

- Never discard an internal refusal and answer `:ok`. The absorbing
  example spends credit without enqueueing and returns `(:ok 0 16)`
  [example: examples/assured/named-stop.lisp].
- Prefer proving the internal precondition from the invariant and deleting
  the refusal branch [example: examples/assured/named-stop.lisp]:

```lisp
(defun enqueue (core)
  (declare (xargs :stobjs core
                  :guard (< (queued core) *cap*)))
  (update-queued (+ 1 (queued core)) core))

(defun issue (core)
  (declare (xargs :stobjs core :guard (core-invp core)))
  (mv-let (code core) (reserve core)
    (if (eq code :ok)
        (let ((core (enqueue core))) (mv :ok core))
      (mv code core))))
```

- Where the boundary cannot prove the precondition, retain the check and
  record a named stop. Preserve the first diagnostic
  [example: examples/assured/named-stop.lisp]:

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

- Keep expected exhaustion as a plain refusal: `reserve` returns
  `:exhausted`. Use `issue-preserves-invariant` and
  `core-stop-keeps-first-reason` for the two proof shapes
  [example: examples/assured/named-stop.lisp].

## 6. Admit named continuations against the world

- Reject pasted forms, undefined continuations and missing state entries.
  The example's `make-event` checks existing guard-verified functions with
  formals `(steps st)`; dispatch returns `:bad-phase` for an unknown phase
  [example: examples/assured/machine.lisp].

```lisp
(defmach copier
  :states (:idle :copy)
  :budget (:steps 32)
  :continuations ((:idle copier-idle) (:copy copier-copy)))

(assert-event (equal (mv-list 2 (copier-run *copier-state-copy* 32 '(40 . 0)))
                     '(32 (8 . 32))))
(assert-event (equal (mv-list 2 (copier-run 7 32 '(40 . 0)))
                     '(:bad-phase (40 . 0))))
```

[example: examples/assured/machine.lisp].

- Do not count obligation names as proved statements. fn2 checks each
  entry is `:owed` or names a registered owed row or generator; it refuses
  "Unregistered or unstated machine obligation"
  [fn: fn2/books/machines.lisp:174-192, 261-267 @127f7b877].

## 7. Check consumers beyond the declaration

- Move derivable consumer machinery into the generator. fn2's review
  found duplicated put-binding, preservation and snapshot/copy/diff
  generators beside the DSL
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:50 @worktree, read 2026-10-29].
- Inspect submitted forms for literal enum comparisons and positional
  access. Translated bodies inline constant values and erase that spelling
  distinction [fn: build/coordinator/fn2/DSL-METATHEORY.md:503, 513-520 @worktree, read 2026-10-29].
- Keep the proposed check's limit explicit: "It checks submitted spelling
  and the common cases. A literal reached through a helper or an unexpanded
  macro passes" [fn: build/coordinator/fn2/DSL-METATHEORY.md:522 @worktree, read 2026-10-29].