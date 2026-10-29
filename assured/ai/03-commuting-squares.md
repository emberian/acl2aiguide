# assured/ai/03. State what a change preserves with commuting squares

Load when proving representation changes, summary adequacy, fused execution,
or schedule swaps. Companion: [Commuting squares](../humans/03-commuting-squares.md).
Copy the events below in their cited books' contexts.

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| Equal answers diverge after one input | Observation equality is not step-closed [example: examples/transport/read-state-teeth.lisp] | 1 |
| Correct steps start from unrelated states | Missing initialization or converter proof [fn: fn2/docs/design/COHERENCE.md:91 @66ff84f4a, read 2026-10-29] | 2 |
| Component proofs miss a broken merge | Generators omit composite operations [fn: fn2/docs/design/COHERENCE.md:112 @66ff84f4a, read 2026-10-29] | 2 |
| Functional instantiation fails | The substituted step obligation can be false [example: examples/transport/read-state-teeth.lisp] | 3 |
| Different machines fail to commute | They share allocator state [example: examples/assured/diamond.lisp] | 4 |
| Composition loses the contract | Relations, labels, or independence changed between pieces [fn: fn2/docs/design/COHERENCE.md:260 @66ff84f4a, read 2026-10-29] | 5 |
| Convergence passes but reply bytes differ | Comparator forgets article numbers [fn: fn2/docs/design/COHERENCE.md:161 @66ff84f4a, read 2026-10-29] | 6 |
| TRACE passes a shared handler bug | Both sides reuse handlers [fn: fn2/docs/design/REVIEW-SINS-20261028.md:87 @66ff84f4a, read 2026-10-29] | 7 |
| Bounded checks become a universal claim | Future closure and coverage remain unproved [fn: fn2/docs/design/COHERENCE.md:750 @66ff84f4a, read 2026-10-29] | 8 |

## 1. Choose a relation that survives continuation

- Do not use equal current answers as the relation without proving step closure.
  Histories `((:read 1))` and `((:read 2))` both count one; another `(:read 1)`
  separates them. Use `rs-count2-rel-not-step-closed` as the counterexample.
  [example: examples/transport/read-state-teeth.lisp]
- Specify `(A, B, R, T, obs, kappa)`: representations, relation, transition
  language, observations, and declared observational loss. Identity loss
  preserves observations exactly.
  [fn: fn2/docs/design/COHERENCE.md:25 @66ff84f4a, read 2026-10-29]
- Allow a label to denote a target word, including the empty word. For partial
  transitions, supply a matching target execution when the source succeeds.
  [fn: fn2/meta/Fn2/Square.lean:172 @dddc32d34]
  [fn: fn2/meta/Fn2/Square.lean:79 @dddc32d34]
- Retain emitted history in semantic state or a monitor. Include refusals,
  effects, distinguishable action prefixes, and crash cuts in the contract;
  endpoint equality cannot recover an earlier differing reply.
  [fn: fn2/docs/design/COHERENCE.md:231 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:249 @66ff84f4a, read 2026-10-29]

## 2. Separate entry, steps, loss, and swaps

- Do not promote an inventory row to a proof. Record whether it is a
  specification, checked instance, assumption, or proved claim.
  [fn: fn2/docs/design/COHERENCE.md:48 @66ff84f4a, read 2026-10-29]
- Distinguish E (equality/function graph), S (forward simulation), B
  (bisimulation), L (restricted lens laws), Q (declared loss), T (certified
  schedule swaps), and X (environment containment). X lies outside the
  representation squares.
  [fn: fn2/docs/design/COHERENCE.md:35 @66ff84f4a, read 2026-10-29]
- Do not infer implementation equality from two simulations into one
  nondeterministic specification; add matching or uniqueness.
  [fn: fn2/docs/design/COHERENCE.md:295 @66ff84f4a, read 2026-10-29]
- Prove **G0**: initialization or conversion establishes admissibility and
  the relation. Step preservation does not prove converter correctness.
  [fn: fn2/docs/design/COHERENCE.md:91 @66ff84f4a, read 2026-10-29]
- Prove **G1** for every admitted transition instance: matching steps or
  words preserve admissibility, relation, and named observations.
  [fn: fn2/docs/design/COHERENCE.md:92 @66ff84f4a, read 2026-10-29]
- For **G1q**, prove retained observations factor through the lossy map and
  its kernel survives the promised future operations. State a read-only
  snapshot contract explicitly when no command congruence is promised.
  [fn: fn2/docs/design/COHERENCE.md:168 @66ff84f4a, read 2026-10-29]
- Prove **G2** for declared-independent occurrences: legal routes, preserved
  occurrence meaning, and endpoints related under a future-closed contract.
  Include enabledness, effects, allocator changes, and scheduler consequences.
  [fn: fn2/docs/design/COHERENCE.md:94 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:169 @66ff84f4a, read 2026-10-29]
- Generate cases for composite operations and shared protocols, including
  merges. Give duplicate absorption its own equation; `f` versus `ff` is
  not an adjacent swap.
  [fn: fn2/docs/design/COHERENCE.md:167 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:171 @66ff84f4a, read 2026-10-29]

## 3. Prove local cases; instantiate the generic execution theorem

- When instantiation fails, test the contract before adding hints. The manual:
  "before such a lemma instance can be used, the system will generate proof obligations".
  Discharge the substituted supporting constraints.
  [:doc lemma-instance]
- For one event on each side, prove preservation per event kind, including
  malformed events; prove observation agreement and initialization separately.
  Keep converter correctness separate from continuation.
  [example: examples/transport/read-state-transport.lisp]
- Reuse the generic fold induction in its book context:
  [example: examples/transport/fold-contract.lisp]

```lisp
(defthm fc-rel-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))
```

- For fused execution, use a word interpretation. Here `fused-h` maps
  `(:recv2 k n m)` to `((:bump k n) (:bump k m))`; the fused side caches
  the total and the reference recomputes it. Prove the step and edge:
  [example: examples/assured/square-paste.lisp]

```lisp
(defthm fused-step-square
  (implies (fused-rel a b)
           (fused-rel (fused-step a l) (ref-run b (fused-h l)))))

(defthm fused-edge
  (implies (fused-rel a b) (equal (fused-obs a q) (ref-obs b q))))
```

- Instantiate the word theorem, including the derived runs and expansion.
  This whole-run event performs no induction of its own:
  [example: examples/assured/square-paste.lisp]

```lisp
(defthm fused-refines-reference
  (implies (fused-rel a b)
           (equal (fused-obs (fused-run a w) q)
                  (ref-obs (ref-run b (fused-expand w)) q)))
  :hints (("Goal" :use ((:functional-instance sq-paste-obs
                         (sq-a-init fused-init) (sq-b-init ref-init)
                         (sq-a-step fused-step) (sq-b-step ref-step)
                         (sq-h fused-h)
                         (sq-a-obs fused-obs) (sq-b-obs ref-obs)
                         (sq-rel fused-rel)
                         (sq-a-run fused-run) (sq-b-run ref-run)
                         (sq-expand fused-expand))))))

(defthm fused-base (fused-rel (fused-init) (ref-init)))
```

- Keep a theorem exhibiting the false step obligation. This mutant omits the
  second chunk from its cached total; the book evaluates totals 5 versus 12:
  [example: examples/assured/square-paste.lisp]

```lisp
(defthm fused-step-bad-breaks-square
  (let ((a (fused-init)) (b (ref-init)) (l '(:recv2 1 5 7)))
    (and (fused-rel a b)
         (not (fused-rel (fused-step-bad a l) (ref-run b (fused-h l)))))))
```

## 4. Earn independence from shared-state behavior

- Reject "different machines" as an independence test. Accept and close share
  the free count; from no free rows and one occupied row, order changes admission.
  Copy the evaluated witness and refutation in the diamond book's context:
  [example: examples/assured/diamond.lisp]

```lisp
(assert-event (equal (nth *admitted* (close-row (accept *start*))) 0))
(assert-event (equal (nth *admitted* (accept (close-row *start*))) 1))

(defthm accept-close-not-diamond
  (not (equal (close-row (accept *start*)) (accept (close-row *start*)))))
```

- Require footprints to describe actual behavior: guards and written values
  depend on declared reads; other positions remain unchanged. Exclude either
  action writing what the other reads or writes.
  [fn: fn2/meta/Fn2/Coherence.lean:138 @dddc32d34]
  [fn: fn2/meta/Fn2/Coherence.lean:206 @dddc32d34]
- Do not generalize the ACL2 companion beyond its theorem: these actions each
  read and write one position. At distinct natural positions they commute:
  [example: examples/assured/diamond.lisp]

```lisp
(defthm footprint-diamond
  (implies (and (natp p) (natp q) (not (equal p q)))
           (equal (at-f p (at-g q s)) (at-g q (at-f p s)))))
```

- Check enabledness separately: mutually disabling actions can have equal
  failed two-step runs without being independent.
  [fn: fn2/meta/Fn2/Coherence.lean:67 @dddc32d34]
- Treat the accept/close result as a refuted independence declaration;
  admission may legitimately depend on reclamation order.
  [fn: fn2/docs/design/COHERENCE.md:851 @66ff84f4a, read 2026-10-29]

## 5. Paste only under the inherited premises

- Do not compose pieces after silently changing their contract.
  [fn: fn2/docs/design/COHERENCE.md:260 @66ff84f4a, read 2026-10-29]
- For vertical pasting, establish that every executed label belongs to the
  supplied catalogue. A covered catalogue does not cover an omitted case.
  [fn: fn2/meta/Fn2/Square.lean:178 @dddc32d34]
  [fn: fn2/meta/Fn2/Coherence.lean:489 @dddc32d34]
- For horizontal pasting, use an explicit sequence of valid adjacent swaps.
  Executable words in the same trace reach equal states under a valid dependency relation.
  [paper: godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf, section 3.2, Theorem 3.10]
- For the general mixed schema, check `R_AB ; approx_B subset-of approx_A ; R_AB`
  with composition read left to right; also preserve declared swaps through
  label interpretation. The relation inclusion alone is insufficient.
  [fn: fn2/docs/design/COHERENCE.md:264 @66ff84f4a, read 2026-10-29]
- Keep the pinned Lean result narrower: one representation edge, partial
  deterministic transitions, exact implementation diamonds, related start,
  and successful run.
  [fn: fn2/meta/Fn2/Coherence.lean:107 @dddc32d34]
- For route-independent occurrence identities, additionally establish residual
  consistency across the two three-swap routes reversing three occurrences.
  [fn: fn2/docs/design/COHERENCE.md:328 @66ff84f4a, read 2026-10-29]

## 6. Keep the observation contract explicit

- Do not use convergence modulo article numbering to claim equal wire replies.
  Q1/WIRE preserves reply bytes; Q12 may retain validated facts and forget
  local numbering. Same-group POSTs are dependent under the former contract.
  [fn: fn2/docs/design/COHERENCE.md:235 @66ff84f4a, read 2026-10-29]
- After a failed diamond, preserve the relevant order or narrow the contract
  explicitly, then prove the resulting transition obligations.
  [fn: fn2/docs/design/COHERENCE.md:731 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:738 @66ff84f4a, read 2026-10-29]

## 7. Read TRACE as differential evidence

- Do not count shared handlers as independently validated semantics. TRACE's
  independent contribution is selection order, including calendar, queues,
  and observation order.
  [fn: fn2/docs/design/REVIEW-SINS-20261028.md:87 @66ff84f4a, read 2026-10-29]
- On `TRACE DIFFERENCE`, inspect pre-state, resulting states, and
  `(status obs visits actions)`; a difference returns `(:fail :trace ...)`.
  [fn: fn2/sim/check-trace.lisp:5 @127f7b877]
- Keep the universal turn refinement and accounting obligations outstanding:
  the pinned statement is `defthm-owed`. Neither passing TRACE nor Lean
  composition discharges the ACL2 instance.
  [fn: fn2/books/reference.lisp:248 @127f7b877]
  [fn: fn2/docs/design/LEAN-METATHEORY.md:32 @66ff84f4a, read 2026-10-29]

## 8. State the boundary beside the conclusion

- Do not infer future closure or schedule-pruning permission from passing
  bounded checks. Report the finite input domain and horizon.
  [fn: fn2/docs/design/COHERENCE.md:750 @66ff84f4a, read 2026-10-29]
- Establish physical environment containment separately from simulation into
  a fault model; native experiments do not prove universal containment.
  [fn: fn2/docs/design/COHERENCE.md:810 @66ff84f4a, read 2026-10-29]
- Prove progress and resource accounting separately; measure wall time.
  Equal finite-prefix observations do not establish liveness or equal costs.
  [fn: fn2/docs/design/COHERENCE.md:130 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/COHERENCE.md:814 @66ff84f4a, read 2026-10-29]
- Compare transported data separately: position maps, converted cuts,
  occurrence identities, and loss descriptors are not settled by thin squares.
  [fn: fn2/docs/design/COHERENCE.md:289 @66ff84f4a, read 2026-10-29]
- Separate generator soundness from completeness. Valid generators composing
  does not prove they connect every intended interchangeable route.
  [fn: fn2/docs/design/COHERENCE.md:189 @66ff84f4a, read 2026-10-29]
