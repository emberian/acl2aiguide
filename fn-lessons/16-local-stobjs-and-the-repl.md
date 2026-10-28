# 16. `with-local-stobj`'s return shape, and the REPL that refuses to redefine

## The wound

The LB lane's continuation, written when it parked on 2026-10-28, lists the
REPL and proof-session pitfalls that "each cost an attempt"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:20-27 @worktree]:

- "ACL2 `with-local-stobj`: the body returns the other values and NOT the
  local stobj: `(with-local-stobj st (mv-let (answer other st) (CALL ... st)
  (mv answer other)))`. A stobj argument must be a variable, never a call:
  bind with `let` first. `loop$` bodies need badged functions: use plain
  recursion in test files."
- "The REPL refuses to redefine a changed function: after editing a book or
  test, stop and restart the session."
- "`start --certify-missing` certifies only a book's DEPENDENCIES, never the
  book itself"; "`--ld` takes a dependency of the session's book, not the
  book itself"; a session stops after its idle timeout, 20 minutes by default.

And from fn's REPL documentation, the trap in loading a book from source:
loading it form by form leaves "its local lemmas in the session as rules its
dependents use", which is why the default loads a from-source book "inside a
single `(encapsulate () ...)` ... so its `local` lemmas stay local as a
certified include keeps them" [fn: docs/proofs.md:537-541 @3bbfc4dca].

## What was done about it

`tools/proof_repl.py` keeps one ACL2 alive per lane behind a socket, loads a
book's certified closure, wraps each sent event in `with-prover-time-limit`,
and reports ACL2's own `Time:` and step count per form, "seconds per attempt
against cached certificates, instead of a closure run per attempt on the
farm"; "A form ACL2 admits there is not a certificate; the event goes into
the book and the book certifies" [fn: docs/proofs.md:489-506 @3bbfc4dca]. The
pitfalls above were not fixed in the tool; they were written into the lane's
continuation for the next seat
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:20 @worktree].

## The lesson

Each of these is ACL2 behaving as documented, and each is cheaper to read
than to rediscover.

- `with-local-stobj` takes "a call of `mv-let` that binds `stobj-name` but
  does not return `stobj-name`", and neither it nor its expansion is "legal
  when typed directly at the top-level loop"; use `top-level` there
  [:doc with-local-stobj], [:doc top-level].
- A stobj formal accepts only "the variable `OBJ`, not merely a term that
  ``evaluates to an obj''"; "instead of `(FOO (UPDATE-FIELD1 3 ST))` write
  `(LET ((ST (UPDATE-FIELD1 3 ST))) (FOO ST))`" [:doc stobj].
- "When `ld-redefinition-action` is `nil`, redefinition is prohibited. In
  that case, an error message is printed upon any attempt to introduce a name
  that is already in use"; the manual calls redefinition "a way to facilitate
  unsafe, but potentially useful, hacking" and points to undoing as "often a
  better way" [:doc ld-redefinition-action]. Undo with `:ubt` [:doc ubt], or
  restart the session.
- The repeatedly evaluated parts of a `loop$` "must be tame", so "all the
  function symbols used in these expressions must be badged" [:doc loop$].
- Load a book's events into a session inside an `encapsulate` when you want
  its `local`s to stay local: `local` events "are processed when the
  encapsulation or book is checked for admissibility ... but are skipped when
  extending the host world" [:doc local].

## The shape to copy

Both stobj shapes, certified, with the two wrong versions recorded as
`must-fail` [example: examples/fn-lessons/local-stobj-shape.lisp]:

```lisp
(defun sum-with-local-tally (xs)
  (declare (xargs :guard (nat-listp xs)))
  (with-local-stobj
   tally
   (mv-let (total tally)
     (let ((tally (tally-add-all xs tally)))
       (mv (tally-n tally) tally))
     total)))

(defun restart-and-add (xs tally)
  (declare (xargs :stobjs tally :guard (nat-listp xs)))
  (let ((tally (update-tally-n 0 tally)))
    (tally-add-all xs tally)))
```

ACL2's refusals of the wrong versions read "Contrary to the declaration that
it is IGNOREd, the variable TALLY is used in the MV-LET expression that binds
TOTAL and TALLY" (returning the local stobj), and "The form (UPDATE-TALLY-N 0
TALLY) is being used, as an argument to a call of TALLY-ADD-ALL, where the
single-threaded object TALLY is required. Note that the variable TALLY is
required, not merely a term that returns such a single-threaded object, so
you may need to bind TALLY with LET" (a call in a stobj position)
[measured: the two `must-fail` bodies of examples/fn-lessons/local-stobj-shape.lisp
sent to the laptop REPL after including the book, ACL2 8.7 / SBCL 2.6.8].
