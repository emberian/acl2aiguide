# assured/ai/05. Transport across representations

Load when replacing a history with a summary or carrying clients across
a representation change. Companion: [Transport across representations](../humans/05-transport.md).
fn coordinator citations retain the humans chapter's `@worktree` read date.

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| `must-fail` passes on a malformed lambda | syntax rejection masks the intended mathematical failure [guide: examples/transport/README.md:193] | 1 |
| equal counts diverge after one event | fixed-bound equality is not step-closed [example: examples/transport/read-state-teeth.lisp] | 2 |
| adequacy proved, converter correctness missing | preservation assumes an already-related pair [example: examples/transport/read-state-transport.lisp] | 2 |
| exact converter equation fails despite equal answers | an unobserved summary component changes [example: examples/assured/summary-upto.lisp] | 3 |
| client transport fails after `defiso` | base correspondences and domain hypotheses still matter [example: examples/transport/cursor-v1.lisp] [example: examples/transport/cursor-iso.lisp] | 4 |
| `:BETA-IMAGE` fails | widened epoch converts outside the old domain [example: examples/transport/cursor-wide.lisp] | 5 |
| `:beta-of-alpha` fails | conversion drops generation [example: examples/transport/cursor-v3-lossy.lisp] | 5 |
| generated proofs mistaken for integration or savings | logical examples leave consumers and served operations to measure and connect [fn: fn2/docs/design/TRANSPORT.md:566 @66ff84f4a, read 2026-10-29] | 6 |

## 1. Make the negative control falsify the intended obligation

- Reject this diagnostic as evidence against the mathematics:
  [guide: examples/transport/README.md:193]

```text
is neither a function symbol nor a pseudo-lambda expression
```

- Use the named observation `rs-h-count2-obs`; inspect an unwrapped failure,
  then prove the witness `rs-count2-rel-step-obligation-false`.
  A refusal alone does not identify the failed obligation.
  [example: examples/transport/read-state-teeth.lisp]
- Keep the bad-compaction control: after `(:read 1) (:read 3)`, the mutant
  reports article 2 read; history and the correct summary report `nil`.
  [example: examples/transport/read-state-teeth.lisp]

## 2. Transport the relation through every suffix

- Do not use equality of counts at bound 2 as the step invariant.
  `((:read 1))` and `((:read 2))` both count 1; after `(:read 1)`, they count
  1 and 2. fn2 incorrectly described this witness as equality "at every bound".
  Strengthen this relation; do not infer that every observation needs strengthening.
  [fn: fn2/docs/design/TRANSPORT.md:282 @66ff84f4a, read 2026-10-29]
  [example: examples/transport/read-state-teeth.lisp]
- Prove the induction over constrained functions once. The fold contract
  exports related admissible initial states, step preservation, and observation
  agreement; `fc-rel-fold` and `fc-obs-fold` apply to any related admissible pair.
  [example: examples/transport/fold-contract.lisp]
- Discharge the instance's supporting constraints. ACL2 generates:
  > proof obligations arising from the replacement of the `fi`'s by the
  > `gi`'s in constraints that ``support'' the lemma to be functionally
  > instantiated
  [:doc lemma-instance]
- Relate the newest-first history to its `(hwm . above)` summary by article
  queries; derive count agreement by induction on the bound.
  [example: examples/transport/read-state-history.lisp]
  [example: examples/transport/read-state-summary.lisp]
  [example: examples/transport/read-state-transport.lisp]

```lisp
(defun-sk rs-same-reads (h s)
  (forall n (equal (rs-h-obs-read h n) (rs-s-obs-read s n))))
```

[example: examples/transport/read-state-transport.lisp]

- Cover `:read`, `:catchup`, and malformed events. History retains malformed
  events without observing them; the summary leaves its state unchanged.
  Then instantiate both conclusions, including the relation parameter.
  [example: examples/transport/read-state-history.lisp]
  [example: examples/transport/read-state-summary.lisp]
  [example: examples/transport/read-state-transport.lisp]

```lisp
(defthm rs-summary-adequate
  (implies (and (rs-h-ok h) (rs-s-ok s) (rs-same-reads h s))
           (and (rs-same-reads (rs-h-fold h j) (rs-s-fold s j))
                (equal (rs-h-obs (rs-h-fold h j) q)
                       (rs-s-obs (rs-s-fold s j) q))))
  :hints (("Goal"
           :in-theory (disable rs-h-ok rs-s-ok rs-h-obs rs-s-obs)
           :use ((:functional-instance fc-rel-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))
                 (:functional-instance fc-obs-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))))))
```

[example: examples/transport/read-state-transport.lisp]

- Prove `rs-summarize-related` separately: conversion produces a related pair.
  Combine it with preservation to obtain `rs-summarize-adequate`.
  [example: examples/transport/read-state-transport.lisp]

## 3. Use the converter graph up to congruence

- When an unobserved component breaks exact commutation, prove the step
  equation up to an equivalence that respects summary steps and observations.
  The parity example refutes exact equality while preserving answers.
  [example: examples/assured/summary-upto.lisp]
- Do not compose arbitrary sound up-to functions without a compatibility
  argument. For monotone functions, compatibility is `f o b <= b o f`;
  compatible functions remain compatible under composition and pointwise union.
  [paper: pous-sangiorgi2019-bisimulation-and-coinduction-enhancements-historical-perspective.pdf, section 5, pp. 7-8]
- Establish the equivalence before congruence. `defequiv` proves the relation
  "Boolean, reflexive, symmetric, and transitive"; `defcong` requires
  "known equivalence relations". Copy the complete generic interface:
  [:doc defequiv] [:doc defcong] [:doc congruence]

```lisp
(encapsulate
  (((gu-h-step * *) => *) ((gu-s-step * *) => *)
   ((gu-h-obs * *) => *) ((gu-s-obs * *) => *)
   ((gu-conv *) => *) ((gu-equiv * *) => *))

  (local (defun gu-h-step (h e) (declare (ignore h e)) nil))
  (local (defun gu-s-step (s e) (declare (ignore s e)) nil))
  (local (defun gu-h-obs (h q) (declare (ignore h q)) nil))
  (local (defun gu-s-obs (s q) (declare (ignore s q)) nil))
  (local (defun gu-conv (h) (declare (ignore h)) nil))
  (local (defun gu-equiv (x y) (equal x y)))

  (defequiv gu-equiv)
  (defcong gu-equiv gu-equiv (gu-s-step s e) 1)
  (defcong gu-equiv equal (gu-s-obs s q) 1)

  (defthm gu-step-equation
    (gu-equiv (gu-s-step (gu-conv h) e) (gu-conv (gu-h-step h e))))

  (defthm gu-edge
    (equal (gu-h-obs h q) (gu-s-obs (gu-conv h) q))))
```

[example: examples/assured/summary-upto.lisp]

- Use `gu-graph-upto-fold` for equivalence to converted history and
  `gu-graph-upto-obs` for equal answers. These constraints are unconditional;
  unlike the first contract, they have no admissibility hypotheses.
  Removing the quantified relation leaves equivalence, congruence, and equations to prove.
  [example: examples/assured/summary-upto.lisp]
- Retain the parity control. `par-equiv` ignores the step counter;
  conversion resets it to zero, while every summary step increments it.
  [example: examples/assured/summary-upto.lisp]

```lisp
(defthm parity-step-not-homomorphism
  (not (equal (par-s-step (par-conv nil) :inc) (par-conv (par-h-step nil :inc))))
  :hints (("Goal" :in-theory (enable par-s-step par-conv par-h-step))))
```

[example: examples/assured/summary-upto.lisp]

## 4. Supply base correspondences before propagating clients

- Do not expect `defiso` to translate arbitrary accessors. Supply translated
  base functions and correspondence theorems in both directions.
  `propagate-iso`: "Currently does not handle mutual recursion."
  [:doc apt::propagate-iso]
- Keep domain hypotheses in client theorems; the unconditional generation
  theorem failed to transport. Use `cur1-p` and `cur2-p` for the intended
  generated names: naming removes trailing `-P` when both predicates have it.
  [example: examples/transport/cursor-v1.lisp]
  [fn: fn2/docs/design/TRANSPORT.md:560 @66ff84f4a, read 2026-10-29]
  [books: kestrel/apt/lift-iso.lisp:827]
- Store the base correspondences as `defthmd`. Enabling a forward
  correspondence in this experiment rewrote through its own conversion map.
  After defining the maps and base functions, use:
  [fn: fn2/docs/design/TRANSPORT.md:562 @66ff84f4a, read 2026-10-29]
  [example: examples/transport/cursor-iso.lisp]

```lisp
(defiso cur1-iso-cur2
  cur1-p cur2-p cur1->cur2 cur2->cur1
  :thm-enable :all-nonguard)

(defthmd cur1-position-->cur2
  (implies (cur1-p row)
           (equal (cur1-position row) (cur2-position (cur1->cur2 row)))))
(defthmd cur2-position-->cur1
  (implies (cur2-p row)
           (equal (cur2-position row) (cur1-position (cur2->cur1 row)))))
```

[example: examples/transport/cursor-iso.lisp]

- Supply the generation and update correspondences too; select the event
  range, then check generated theorem names in the world.
  [example: examples/transport/cursor-iso.lisp]

```lisp
(apt::propagate-iso cur1-iso-cur2
  ((cur1-position cur2-position cur1-position-->cur2 cur2-position-->cur1
                  (cur1-p) => *)
   (cur1-generation cur2-generation cur1-generation-->cur2 cur2-generation-->cur1
                    (cur1-p) => *)
   (cur1-with-position cur2-with-position
                       cur1-with-position-->cur2 cur2-with-position-->cur1
                       (cur1-p *) => cur1-p))
  :first-event cur1-position-of-cur1-with-position
  :last-event cur1-advance-keeps-token)

(assert-event (theorem-namep 'cur2-advance-monotone (w state)))
(assert-event (theorem-namep 'cur2-advance-idempotent (w state)))
(assert-event (theorem-namep 'cur2-advance-rowp (w state)))
(assert-event (theorem-namep 'cur2-advance-keeps-token (w state)))
```

[example: examples/transport/cursor-iso.lisp]

## 5. Separate image failure from information loss

- On widening epoch from u28 to u32, expect:
  [example: examples/transport/cursor-wide.lisp]

```text
The proof of the :BETA-IMAGE applicability condition fails
```

- Apply the manual's obligation: "The conversion [beta] maps the domain [B]
  to the domain [A]" (brackets replace mathematical symbols).
  Epoch `2^28`, sequence 0 maps to position `2^60`, outside u60.
  Use `cur2-wide-beta-image-false`; the witness is a theorem because direct
  conversion violates its narrower guard. `:guard-thms nil` isolates image failure.
  [:doc defmapping]
  [example: examples/transport/cursor-wide.lisp]
- On dropping generation, inspect `:beta-of-alpha`: beta "is left inverse of"
  alpha. Generations 5 and 6 at registration 7, position 100 collapse to one
  image but disagree on token 5. Keep `no-v3-token-check`, which rules out
  an unconstrained replacement agreeing with both answers.
  [:doc defmapping]
  [example: examples/transport/cursor-v3-lossy.lisp]

## 6. Count consumers and preserve the boundary

- Do not confuse wiping pre-release data with preserving client proofs;
  fn2's corrected scope separates those tasks.
  [fn: fn2/docs/design/TRANSPORT.md:27 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/TRANSPORT.md:31 @66ff84f4a, read 2026-10-29]
- Budget the remaining work: A supplies event lemmas, converter correctness,
  and observations; B supplies domains, inverses, and base correspondences.
  `fc-rel-fold` is not B's composition engine.
  [fn: fn2/docs/design/COHERENCE.md:789 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:794 @66ff84f4a, read 2026-10-29]
- Measure before generating another DSL. The logical cursor experiment on
  laptop ACL2 8.7 used 72 handwritten lines for 71 generated statement and
  definition lines, excluding generated proof instructions.
  [guide: examples/transport/README.md:113]
  [guide: examples/transport/README.md:130]
- Keep claims scoped: summary adequacy does not establish retained historical
  answers; cursor transport does not establish correspondence to served columns
  or scaling to generated accessor families.
  [fn: fn2/docs/design/TRANSPORT.md:566 @66ff84f4a, read 2026-10-29]
