# assured/ai/04. The one-minute rule and certify-cost discipline

Load when writing a theorem generator, diagnosing certification growth, or
splitting a slow book. The terse twin of `assured/humans/04-certify-cost.md`.

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| many useless NTH frames | per-column generic rules match unrelated fields [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read 2026-10-29] | 2, 3 |
| setter proofs grow faster than field count | each field reopens the whole recognizer and shape invariant [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:208-216 @worktree, read 2026-10-29] | 4, 5 |
| time rises while steps fall | steps alone do not capture certification cost [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:227-229 @worktree, read 2026-10-29] | 2 |
| the same declaration slows after loading the core | generated proofs inherit the includer's theory [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:214 @worktree, read 2026-10-29] | 5 |
| assembly certifies but exceeds a minute | generation stages accumulated in one book [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:25 @worktree, read 2026-10-29] | 1, 7 |
| a split hides growing per-declaration work | book boundaries do not enforce the generator's cost contract [fn: build/coordinator/fn2/DSL-METATHEORY.md:382 @worktree, read 2026-10-29] | 6 |

## 1. Enforce the limit per book

- Treat a successful but slow certification as work to fix. Keep the rule:
  "no book should be over 1m" [fn: commit message of 1fa1fe24b].
- Measure fresh certification, per book. Use ACL2's **CERTIFY-BOOK Time**
  summaries; W1 specifies these rather than shell elapsed time or proof-load
  estimates, with every book "forced fresh" [fn:
  build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:9 @worktree, read
  2026-10-29].
- Preserve the statements and proof discipline: "No statement changed, no
  step limit raised, no skip-proofs". W1 reduced the slowest book from
  902.39 s to 46.84 s and summed book times from 1,876 s to 284 s,
  measured fresh with two jobs [fn: commit message of 1fa1fe24b].

## 2. Diagnose time and rule applications, not steps alone

- Suspect broad linear rules when time grows much faster than steps.
  The NTH example gives every NTH term a candidate from every column's
  generic family; the field-specific family offers one candidate per
  field. The step counter misses that linear-arithmetic work
  [example: examples/assured/nth-cost.lisp].
- Compare several sizes. These measurements isolate the same theorem with
  specific rules alone and with both families enabled
  [example: examples/assured/nth-cost.lisp]:

| fields N | specific rules only | both families enabled |
|---:|---|---|
| 12 | 0.00 s, 1,164 steps | 0.04 s, 1,659 steps |
| 24 | 0.01 s, 2,292 steps | 0.50 s, 3,879 steps |
| 36 | 0.02 s, 3,420 steps | 2.07 s, 6,675 steps |

[measured: REPL driver generating the book's two theorems at N = 12, 24,
36 (the bound raised to 2^60 for N = 36), the Time and "Prover steps
counted" lines of each DEFTHM summary, ACL2 8.7, SBCL 2.6.8, laptop,
2026-10-29].

- Inspect accumulated persistence and per-event certification time by
  event family. W1 found 1,090,404 NTH frames, 1,084,764 useless;
  unrelated array rules each made 13,724 unsuccessful attempts [fn:
  build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read
  2026-10-29].

## 3. Use broad facts inside the generator; export narrow facts

- When every field's rule matches every `(nth i xs)`, derive the typed
  accessor API with those rules, then disable them. Keep them available
  by explicit hint; leave field-specific facts enabled
  [fn: commit message of 1fa1fe24b].
- State the field-specific fact about the reader's exact term,
  `(nth i (nth K st))`, so it matches its own field [fn:
  fn2/books/columns.lisp:505-522 @127f7b877].
- Reproduce the scope change with the definitions in `nth-cost.lisp`.
  Both theorems prove the same bound; the second re-enables the costly
  generic family [example: examples/assured/nth-cost.lisp].

```lisp
(nc-columns 24)

(nc-generic nil 24)

(defthm field-sum-bound-specific
  (nc-field-sum-bound 24)
  :rule-classes nil)

(nc-generic t 24)

(defthm field-sum-bound-both
  (nc-field-sum-bound 24)
  :rule-classes nil)
```

- Apply the same closure in the real emitter: `defcols` uses its per-array
  NTH facts for reader theorems, then disables them at the expansion's end
  [example: examples/assured/columns.lisp].

## 4. Prove the family once; instantiate per field

- Stop repeated whole-table expansion in setter WFP and type proofs.
  R5a replaced it with column-length preservation proved once over an
  index, opaque table WFP, and field instances of type/shape facts [fn:
  build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:216 @worktree, read
  2026-10-29].
- Put the list induction in a template over a constrained value predicate.
  Copy these template events from `columns.lisp`
  [example: examples/assured/columns.lisp].

```lisp
(encapsulate (((ac-valuep *) => *))
  (local (defun ac-valuep (x) (natp x))))
(defun ac-valuesp (xs)
  (if (atom xs) (eq xs nil)
    (and (ac-valuep (car xs)) (ac-valuesp (cdr xs)))))
(defthm ac-valuesp-nth
  (implies (and (ac-valuesp xs) (natp i) (< i (len xs)))
           (ac-valuep (nth i xs))))
(defthm ac-valuesp-update
  (implies (and (ac-valuesp xs) (natp i) (< i (len xs)) (ac-valuep v))
           (ac-valuesp (update-nth i v xs))))
(defthm ac-valuesp-resize
  (implies (and (ac-valuesp xs) (ac-valuep v))
           (ac-valuesp (resize-list xs n v))))
```

- Instantiate those facts per column with `:functional-instance`; do not
  repeat induction. This complete helper uses `ac-sym` and `ac-width`
  from the same book [example: examples/assured/columns.lisp].

```lisp
(defun ac-array-facts (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (let* ((p (ac-sym name "-" (caar cols) "$AP"))
           (w (ac-width (cadar cols)))
           (subst `((ac-valuep (lambda (x) (unsigned-byte-p ,w x)))
                    (ac-valuesp ,p))))
      (append
       `((defthm ,(ac-sym p "-NTH-NATP")
           (implies (and (,p xs) (natp i) (< i (len xs))) (natp (nth i xs)))
           :rule-classes :type-prescription
           :hints (("Goal" :use ((:functional-instance ac-valuesp-nth ,@subst)))))
         (defthm ,(ac-sym p "-NTH-BOUND")
           (implies (and (,p xs) (natp i) (< i (len xs))) (< (nth i xs) ,(expt 2 w)))
           :rule-classes :linear
           :hints (("Goal" :use ((:functional-instance ac-valuesp-nth ,@subst)))))
         (defthm ,(ac-sym p "-OF-UPDATE-NTH")
           (implies (and (,p xs) (natp i) (< i (len xs)) (unsigned-byte-p ,w v))
                    (,p (update-nth i v xs)))
           :hints (("Goal" :use ((:functional-instance ac-valuesp-update ,@subst)))))
         (defthm ,(ac-sym p "-OF-RESIZE-LIST")
           (implies (and (,p xs) (unsigned-byte-p ,w v)) (,p (resize-list xs n v)))
           :hints (("Goal" :use ((:functional-instance ac-valuesp-resize ,@subst))))))
       (ac-array-facts name (cdr cols))))))
```

## 5. Pin the proof theory; close recognizers

- If prior declarations or core includes inflate field proofs, capture
  the generator book's theory with `deftheory` and install it locally in
  each expansion [fn:
  fn2/books/columns.lisp:564-567, 715-718 @127f7b877].
- Keep whole-table recognizers closed at definition; open them only in
  named bridges. Allow "at most **one linear-sized bridge per family**"
  [fn:
  build/coordinator/fn2/DSL-METATHEORY.md:377-382 @worktree, read
  2026-10-29].
- Localize other costly automation when measurements identify it.
  One owner-lookup guard spent 32.12 of 36.61 s in tau; disabling tau
  there reduced it to 2.72 s [fn:
  build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:21 @worktree,
  read 2026-10-29].

## 6. State the cost contract; distinguish plans from gates

- Do not treat a passing small declaration as evidence of bounded growth.
  Measure the curve: R5a's 19-, 29-, and 41-field declarations took
  8.76, 30.42, and 104.72 s before the repair; 1.64, 2.44, and 4.42 s
  afterward [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:208-212
  @worktree, read 2026-10-29].
- Specify affine budgets, with constants per template version and
  toolchain. Use `F` for storage/layout fields, `A` for declared arms
  and handlers, and `H` for core children [fn:
  build/coordinator/fn2/DSL-METATHEORY.md:368-375 @worktree, read
  2026-10-29].

```text
generated theorem count <= c0 + cF*F + cA*A + cH*H
generated prover steps  <= b0 + bF*F + bA*A + bH*H
```

- Implement the planned structural gate by counting admitted expansion
  events and refusing child-pair matrices. Implement the planned cost
  gate with fixed affine step budgets at 10, 20, 32, and 64 fields;
  retain the binding per-book 60 s limit beside those budgets [fn:
  build/coordinator/fn2/DSL-METATHEORY.md:377-382 @worktree, read
  2026-10-29].
- Preserve the recorded status: fixtures exist at `127f7b877`; the gates
  do not [fn:
  fn2/tests/columns-cost-unit-10.lisp, columns-cost-unit-20.lisp,
  columns-cost-unit.lisp @127f7b877].
- Keep template emission inside ACL2's admission process: "a template
  emitter is not a trusted proof rule: ACL2 admits every resulting theorem"
  [fn:
  build/coordinator/fn2/DSL-METATHEORY.md:323 @worktree, read 2026-10-29].

## 7. Split at generation boundaries or semantic stages

- When assembly exceeds the limit, split at real generation boundaries:
  index/directory, core, access, callbacks, dispatch, reference.
  Preserve public include paths and verify every original event occurs
  exactly once, in its original order [fn:
  build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:25 @worktree, read
  2026-10-29].
- When one operation's preservation proofs dominate, split its body at
  semantic stages, prove each stage's contracts, then prove composition
  through those contracts. R5a's flight/selection split reduced the
  preservation family from 593.22 s to 50.79 s [fn:
  build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:218-222 @worktree,
  read 2026-10-29].
- Choose the semantic boundary yourself: the planned composition kit
  "does not find a good semantic stage boundary by itself" [fn:
  build/coordinator/fn2/DSL-METATHEORY.md:386 @worktree, read
  2026-10-29].
- Keep fixing the generator after splitting: "Splitting books does not
  excuse growing per-declaration proof work" [fn: build/coordinator/fn2/DSL-METATHEORY.md:382
  @worktree, read 2026-10-29].