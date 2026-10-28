# 17. A wrapped session read one level short, and an answer that read as success

## The wound

"The served command chain is four session records deep: an auth session ...
over a peer session ... over a POST session ... over the reader session.
Every wrapper's base accessor descends exactly one level, and all three of
them read `car`. So a call that stops one level short is not a type error the
prover sees; it is a plausible value the callee answers"
[fn: docs/proof-style.md:800-806 @3bbfc4dca]. Four such misses shipped on
2026-09-20: `fn-own-conn-boundedp` tested the POST shape on the whole
connection session, so "ADVANCE became a silent no-op and every connection
was dropped after one read"; `books/served.lisp` reached one wrapper short "so
POST emitted neither 240 nor 441"; the same short reach in its test book; and
`fn-served-transit-outcome` handed the whole session to
`fn-peer-transit-outcome`. "Five more were found by the check below, four of
them in `books/owner-config.lisp`, where the reconfiguration guard read the
PEER NAME where it meant the reader's selected group"
[fn: docs/proof-style.md:808-816 @3bbfc4dca].

The POST miss stayed invisible for a day because of the callee's answer:
`fn-nntp-post-outcome` "used to answer a non-`fn-post-sessionp` argument with
NO EFFECTS, which is not accepted, refused or uncertain: it is a fourth thing
that reads as success" [fn: docs/proof-style.md:829-833 @3bbfc4dca].

## What was done about it

Three rules, "and the third is machinery" [fn: docs/proof-style.md:818 @3bbfc4dca]:

1. "Name the walk once, in the book that owns the outer wrapper"
   (`fn-peer-reader-session`, `fn-auth-post-session`,
   `fn-auth-reader-session`).
2. "They are macros, not functions. Each expands to exactly the term the call
   sites already spell, so the name costs no theorem, no rule, no export entry
   and no re-proof --- which is what let every site be converted at once".
3. "A wrongly-shaped session is answered distinguishably, never benignly": it
   now answers 403, and `fn-post-outcome-separates-a-malformed-session` states
   that the fourth outcome differs from the other three
   [fn: docs/proof-style.md:820-835 @3bbfc4dca].

`tools/session_depth.py` runs in `make check`: it "infers the session level of
every formal from the calls each definition makes" and fails on a base
accessor at the wrong level; its blind spots (a session round-tripped through
the shared result record, a session stored in another field, a formal no call
constrains, other macros) "are the places to read by hand"
[fn: docs/proof-style.md:837-854 @3bbfc4dca].

## The lesson

When records nest, give each level a recognizer that the others cannot
satisfy (a distinct tag), and make each callee's guard name its level's
recognizer; then a short reach is a failed guard proof at definition time
instead of a plausible value at run time: guard verification takes place at
definition time when a guard is supplied, and its point "is to ensure that
during evaluation of an expression without free variables, no guard violation
takes place" [:doc verify-guards]. Name each multi-level walk once; a macro is
enough, because "Macroexpansion occurs when a form is read in, i.e., before
the evaluation or proof of that form is undertaken" [:doc defmacro]. And a function
that receives a value outside its domain returns an outcome that no caller
can mistake for success.

## The shape to copy

Two tagged levels, the walk as a macro, and the same short reach admitted
under a weak guard and refused under a level guard
[example: examples/fn-lessons/tagged-levels.lisp]:

```lisp
(defun post-sessionp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :post) (natp (cdr x))))

(defun auth-sessionp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :auth) (post-sessionp (cdr x))))

(defmacro auth-post-session (a) `(cdr ,a))

(defun post-count (s)
  (declare (xargs :guard (post-sessionp s)))
  (cdr s))

(defun auth-post-count (a)
  (declare (xargs :guard (auth-sessionp a)))
  (post-count (auth-post-session a)))
```

Under `(declare (xargs :guard (consp s)))` the short version `(post-count-weak
a)` is admitted and answers `(:post . 3)` for `'(:auth :post . 3)`; under the
level guard ACL2 refuses `(post-count a)` with the checkpoint `(IMPLIES (AND
(CONSP A) (EQUAL (CAR A) :AUTH) ...) (< (CDDR A) 0))`, the unprovable residue
of `(post-sessionp a)` [measured: the `must-fail` body of
examples/fn-lessons/tagged-levels.lisp sent to the laptop REPL after including
the book, ACL2 8.7 / SBCL 2.6.8].
