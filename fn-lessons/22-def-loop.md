# 22. `def-loop`: 850 identical inductions, then one bridge per shape

## The wound

In the logic an `mbe` "equals `logic-code`", while in a guard-verified body
"only the `:exec` code is evaluated" [:doc mbe], so fn wrote each list
function twice: "a structural recursion
is the `:logic` body the rewriter sees; an accumulator loop `NAME-loop` is
the `:exec` body that runs in constant stack; a local bridge
`NAME-loop-is-revappend` states that the loop is `revappend` of the
accumulator onto the recursion; and two `verify-guards` close the `mbe`.
Written by hand that is twenty-six lines, one induction under
`minimal-theory` and two guard proofs per loop, 850 inductions tree-wide, and
every one of them the same induction" [fn: books/def-loop.lisp:5-12 @3bbfc4dca].
The inventory of 2026-10-01: "1,168 `mbe` forms in 269 books; 494 `defun
fn-*-loop` ...; 471 `:exec (fn-*-loop ...)` wrappers; 850
`-loop-is-`/`-is-rev`/`-exec-is-` equivalence lemmas; 294 `verify-guards` on
loops; 2,034 `revappend` sites; 167 books carry the twin", about 13,000 lines;
the books that carry it took "594 s of the 4,953 s certification CPU in the
largest manifest" [fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:22,86-92 @worktree].

## What was done about it

`books/def-loop.lisp` proves each shape's bridge once: "each SHAPE's bridge is
proved ONCE, over constrained functions that have no axioms (`fn-dl-f`,
`fn-dl-while`, ...), and every instance obtains its bridge by
`:functional-instance` of that one theorem. The obligation ACL2 generates for
the instance is the definitional equation of `NAME` and of `NAME-loop` under
the substitution, which one unfold of each discharges in `minimal-theory`: no
instance induction, no instance hint" [fn: books/def-loop.lisp:14-21 @3bbfc4dca].
The library theorem for `:map`:

```lisp
(defthm fn-dl-map-loop-is-revappend
  (equal (fn-dl-map-loop dl-xs dl-acc) (revappend dl-acc (fn-dl-map dl-xs)))
  :hints (("Goal" :induct (fn-dl-map-loop dl-xs dl-acc))))
```
[fn: books/def-loop.lisp:170-172 @3bbfc4dca]. It emits the loop, the wrapper
with the `mbe`, the local bridge, both `verify-guards`, a disable of the loop
"and a row in the world table `fn-generated` naming what was generated"
[fn: books/def-loop.lisp:60-67 @3bbfc4dca], and it says what it does not do
("a loop that steps by other than `(cdr XS)` ..., a loop that threads a
stobj AND accumulates ..., `defexec`. Those stay by hand with a `; GEN:
def-loop` marker") [fn: books/def-loop.lisp:125-128 @3bbfc4dca]. D62 re-adopted
it with "The 494 loop twins and 285 representation twins are a drain-down
backlog" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:34 @worktree];
the runtime contract reuses the method ("an executable instance obtains them
by `:functional-instance` (books/def-loop.lisp's manner)")
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca].

At `origin/dev` the drain is part-way: 360 `def-loop` forms in 153 books,
beside 221 `defun fn-*-loop` definitions still written by hand in 121 books
and 73 hand `-loop-is-revappend` theorems in 38 books
[measured: `git -C ~/dev/fn grep -c -E '^ *\(def-loop ' 3bbfc4dca -- books`,
`... '^\(defun fn-[^ ]*-loop '`, `... '\(defthm fn-[^ ]*-loop-is-revappend'`,
summed, 2026-10-28, laptop].

## The lesson

When the same proof recurs, prove it once over constrained functions and
obtain each instance by functional instantiation; the per-instance obligation
is then the instance's definitions, not a new induction. The mechanism:
`(:functional-instance lmi (f1 g1) ... (fn gn))` "denotes the formula
obtained by functionally instantiating the formula denoted by `lmi`,
replacing `fi` by `gi`", after ACL2 generates "proof obligations arising from
the replacement of the `fi`'s by the `gi`'s in constraints that ``support''
the lemma" [:doc lemma-instance], and a function with no constraints is
introduced by an `encapsulate` with a local witness [:doc encapsulate]. Wrap
the pattern in a macro so the instance is one form, and record what the
macro generated where a tool can read it. Then delete the hand instances, by
tool, in the landing that introduces the macro (lesson 01).

## The shape to copy

The idea in miniature, certified: one constrained element function, the
shape and its bridge proved once by induction, and a concrete loop whose
bridge is a `:functional-instance` in `minimal-theory` with no induction
[example: examples/fn-lessons/loop-bridge-once.lisp]:

```lisp
(encapsulate
  (((lb-f *) => *))
  (local (defun lb-f (x) x)))

(defun lb-map (xs)
  (if (consp xs)
      (cons (lb-f (car xs)) (lb-map (cdr xs)))
    nil))

(defun lb-map-loop (xs acc)
  (if (consp xs)
      (lb-map-loop (cdr xs) (cons (lb-f (car xs)) acc))
    (revappend acc nil)))

(defthm lb-map-loop-is-revappend
  (equal (lb-map-loop xs acc) (revappend acc (lb-map xs)))
  :hints (("Goal" :induct (lb-map-loop xs acc))))

(defun double-all-loop (xs acc)
  (declare (xargs :guard (and (rational-listp xs) (true-listp acc))
                  :verify-guards nil))
  (if (consp xs)
      (double-all-loop (cdr xs) (cons (* 2 (car xs)) acc))
    (revappend acc nil)))

(defun double-all (xs)
  (declare (xargs :guard (rational-listp xs) :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (cons (* 2 (car xs)) (double-all (cdr xs)))
                nil)
       :exec (double-all-loop xs nil)))

(local
 (defthm double-all-loop-is-revappend
   (equal (double-all-loop xs acc) (revappend acc (double-all xs)))
   :hints (("Goal"
            :use ((:functional-instance lb-map-loop-is-revappend
                                        (lb-f (lambda (x) (* 2 x)))
                                        (lb-map double-all)
                                        (lb-map-loop double-all-loop)))
            :in-theory (union-theories '(double-all double-all-loop)
                                       (theory 'minimal-theory))))))

(verify-guards double-all-loop)
(verify-guards double-all)
```

fn's macro adds the shapes (`:map`, `:take`, `:sum`, `:concat`, `:into`, and
options for early stop, filters, tails and threaded state), the refusals at
expansion and the world-table row [fn: books/def-loop.lisp:23-128 @3bbfc4dca].
Chapter `humans/02-rewriting-theories-books.md` section 2.9.3 explains
functional instantiation with its own example.
