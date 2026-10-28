# 23. Teeth: statements approved without a counterexample search, and a `must-fail` that proves nothing

## The wound

On the rewrite's first day the coordinator approved three statement packets
as "faithful" or "approved", and "the same three packets held 3, 2 and 5
false statements that Codex or a proof attempt found"
[fn: build/coordinator/PROCESS-AUDIT-20261009.md:60 @worktree]. The cost: "10
false statements in three approved packets cost three Codex rounds, two packet
revisions each for A and C, and one 52-minute Sonnet run to find the same five
that Codex had found" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:78 @worktree];
that run's "proof attempts found 5 of 8 statements false (`fn-octets-p`
missing)" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:41 @worktree]. Of
seven read-only reviews that day, "5 of 7 found a false statement or unsound
claim" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:59 @worktree].

The sibling project paid the same way in Lean on 2026-08-07: a keystone
(OB-2, depth composition) landed statement-only and passed a statement-level
audit, and the proof lane then reported "the audited statement is FALSE,
machine-checked". In its words, paraphrased to ASCII: at the empty index set
the hypothesis constrained the error function only on that set, so the
constant function -1 satisfied it vacuously, while the conclusion demanded
`0 <= (t + k) * (-1) < 0` of a nonnegative probability [cv: ad44eec2#263].

The ACL2-specific trap is the teeth that look like evidence and are not: "Never
a general negated `must-fail`: it proves that the prover could not find a
proof, which is not a counterexample, and it loops when the negation is
unprovable rather than false" [fn: docs/proof-style.md:381-383 @3bbfc4dca].
fn's suspect detector, which flags tautology-shaped theorems, states its own
limit: "It cannot see a theorem that is true, non-trivial, and about the wrong
subject", and "The absence of a flag is not evidence of strength. Teeth are"
[fn: docs/proofs.md:227-235 @3bbfc4dca].

## What was done about it

- The teeth contract: "A keystone ships with a reachable non-degenerate
  witness and one concrete violating value per hypothesis, each an
  `assert-event` on the negated conclusion", made a macro, `defteeth`, which
  binds the teeth to the theorem as the world stores it and runs the
  witnesses under the guards [fn: docs/proof-style.md:349-367 @3bbfc4dca].
- "If no violating value exists for a hypothesis, the hypothesis is
  unnecessary: delete it from the theorem and say so"; where a violating value
  exists but cannot be evaluated, a `must-fail` of the weakened statement is
  labelled `; teeth: prover-refusal REASON` and counted apart
  [fn: docs/proof-style.md:383-394 @3bbfc4dca].
- The audit's change: "a packet is "approved to prove" only after each
  keystone has run an ACL2 `test?` counterexample search and carries its
  satisfiable and teeth witnesses"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:79 @worktree].
- After the cut, non-vacuity is owed once, at the top-level theorems, as
  checked `must-fail` books and a satisfiable-premise witness per theorem
  [fn: OWED.md:11-21 @3bbfc4dca].

## The lesson

A statement is not reviewed until it has been run: a positive witness where
every hypothesis holds and the step does something, and for each hypothesis a
concrete value where that hypothesis fails and the conclusion fails. Check
both with `assert-event`, which checks "that evaluation of an expression
returns a non-`nil` value, causing an error otherwise" [:doc assert-event]
(chapter `humans/02-rewriting-theories-books.md` section 2.10.8). Hunt the degenerate corners first: empty sets,
zero, values outside the intended type. A hypothesis with no violating value
is deleted. A `must-fail` records only that the prover refused, which is the
weakest teeth there is (chapter 02 section 2.10.9).

## The shape to copy

A keystone with its witness and per-hypothesis teeth, where the search for
the second hypothesis's teeth finds none and the statement loses it
[example: examples/fn-lessons/teeth-witness.lisp]:

```lisp
(defun bounded-push (x xs cap)
  (declare (xargs :guard (true-listp xs)))
  (if (< (len xs) (nfix cap))
      (cons x xs)
    xs))

; Positive witness: reachable, non-degenerate (the push happened).
(assert-event
 (let ((xs '(a)) (cap 2))
   (and (natp cap) (<= (len xs) cap)
        (equal (bounded-push 'b xs cap) '(b a))
        (<= (len (bounded-push 'b xs cap)) cap))))

; Teeth for (<= (len xs) cap): that hypothesis false, the conclusion false.
(assert-event
 (let ((xs '(a b c)) (cap 2))
   (and (natp cap)
        (not (<= (len xs) cap))
        (not (<= (len (bounded-push 'z xs cap)) cap)))))

; No teeth exist for (natp cap): NFIX sends non-naturals to 0.
(assert-event
 (and (let ((xs nil) (cap 1/2))
        (and (not (natp cap)) (<= (len xs) cap)
             (<= (len (bounded-push 'z xs cap)) cap)))
      (let ((xs '(a)) (cap 3/2))
        (and (not (natp cap)) (<= (len xs) cap)
             (<= (len (bounded-push 'z xs cap)) cap)))))

(defthm bounded-push-respects-cap
  (implies (<= (len xs) cap)
           (<= (len (bounded-push x xs cap)) cap)))
```

fn's own instances are in `tests/acl2/acceptance-tests.lisp` and
`tests/acl2/retention-tests.lisp` [fn: docs/proof-style.md:369-379 @3bbfc4dca];
its macro form is `(defteeth NAME :claim (((L H) ...) C) ...)`
[fn: docs/proof-style.md:353 @3bbfc4dca].
