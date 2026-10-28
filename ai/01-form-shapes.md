# AI 01. Form shapes: copy these, do not guess

Load this whole before writing ACL2. Every shape below is cut from a book under
`examples/shapes/` that certified with `examples/certify.sh` on the laptop
(ACL2 8.7, SBCL 2.6.8); the book is named under each shape. Copy the shape,
rename, and keep the structure. Where a shape has a wrong twin that ACL2
refuses, the book keeps the wrong twin as a `local` `must-fail` and the error
text is quoted here. Pitfalls are ranked in `ai/00-pitfalls-first.md`; this
chapter is the forms.

Rules for every book you write:

- Start with `(in-package "ACL2")` (or your package, section 16).
- Include only certified books, with `:dir :system` for community books;
  "Never use absolute paths" [:doc best-practices].
- Make every `must-fail` `local`: "If a book contains a non-local form that
  causes proofs to be done, such as one of the form `(must-fail (thm ...))`,
  then it might not be possible to include that book"
  [books: std/testing/must-fail.lisp:17].
- Certify the book yourself before you cite or report it (section 18).

## 1. `defun`: `:guard`, `:measure`, `:verify-guards nil`, `verify-guards`

```lisp
(defun count-down (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (count-down (- n 1) (cons n acc))))
```

When: every definition you will execute. The measure must satisfy `o-p` and
decrease on each recursive call "under the hypothesis that all the tests ruling
the call are satisfied" [:doc defun]; `(nfix n)` is a natural, hence an `o-p`
[:doc o-p].

Deferred guards, the guard fact as a `:rule-classes nil` lemma, supplied by
`:use` in the one event that needs it:

```lisp
(defun sum-nats (x)
  (declare (xargs :guard (nat-listp x) :verify-guards nil))
  (if (endp x) 0 (nat-add (car x) (sum-nats (cdr x)))))

(defthm natp-of-sum-nats
  (implies (nat-listp x) (natp (sum-nats x)))
  :rule-classes nil)

(verify-guards sum-nats
  :hints (("Goal" :use ((:instance natp-of-sum-nats (x (cdr x)))))))

(assert-event (eq (symbol-class 'sum-nats (w state)) :common-lisp-compliant))
```

- `:verify-guards nil` admits the logic and leaves the function `:ideal`
  (not guard-verified); the book asserts both classes
  [example: examples/shapes/defun-guards.lisp].
- Guard hints on a `defun` go in `:guard-hints`, "to be used during the guard
  verification proofs as opposed to the termination proofs"; `:hints` are for
  termination [:doc xargs].
- "An equality that exists to discharge a guard or an `mbe` obligation is not a
  rewrite rule. It is stated once, `:rule-classes nil`, and used by `:use`"
  [fn: docs/proof-style.md:242 @3bbfc4dca].
- Check the class from the world, not from the absence of an error:
  `(symbol-class 'f (w state))` is `:common-lisp-compliant` only for a
  guard-verified function [example: examples/shapes/defun-guards.lisp].

Book: `examples/shapes/defun-guards.lisp`.

## 2. `defthm` and its rule classes

One theorem per class, each followed in the book by a goal that needs it
[example: examples/shapes/rule-classes.lisp].

```lisp
(defthm cnt-of-append                       ; :rewrite, the default
  (equal (cnt (append x y)) (+ (cnt x) (cnt y))))

(defthm cnt-of-rv                           ; :rewrite with :corollary
  (equal (cnt (rv x)) (cnt x))
  :rule-classes ((:rewrite :corollary (equal (cnt (rv x)) (cnt x)))))

(defthm true-listp-of-firsts                ; :type-prescription
  (true-listp (firsts x))
  :rule-classes :type-prescription)

(defthm okp-forward                         ; :forward-chaining
  (implies (okp x) (and (consp x) (integerp (car x))))
  :rule-classes ((:forward-chaining :trigger-terms ((okp x))))
  :hints (("Goal" :in-theory (enable okp))))

(defthm cnt-firsts-bound                    ; :linear
  (<= (cnt (firsts x)) (cnt x))
  :rule-classes :linear)

(defthm cnt-two-at-a-time                   ; :definition (alternative body)
  (equal (cnt x)
         (if (consp x)
             (if (consp (cdr x)) (+ 2 (cnt (cddr x))) 1)
           0))
  :rule-classes ((:definition :controller-alist ((cnt t)))))

(defthm drop-suggests-tk-induction          ; :induction (no proof obligation)
  t
  :rule-classes ((:induction :pattern (drop n x) :scheme (tk n x))))

(defthm smallp-compound-recognizer          ; :compound-recognizer
  (implies (smallp x) (and (integerp x) (<= 0 x)))
  :rule-classes :compound-recognizer)

(defequiv lequiv)                           ; :equivalence
(defcong lequiv equal (cnt x) 1             ; :congruence
  :hints (("Goal" :in-theory (enable lequiv)
                  :use ((:instance cnt-of-lfix-direct (x x))
                        (:instance cnt-of-lfix-direct (x x-equiv))))))

(defthm cnt-of-rv-rv-fact                   ; no rule: for :use and :by only
  (equal (cnt (rv (rv x))) (cnt x))
  :rule-classes nil)
```

When:

- Default to `:rewrite`; "new ACL2 users rely almost exclusively on
  (conditional) rewrite rules", and `:type-prescription`/`:forward-chaining`
  for type facts are the "slightly bolder approach" [:doc rule-classes].
- `:forward-chaining` for a fact you want in the context whenever its trigger
  appears; it relieves hypotheses by "type reasoning, evaluation of ground
  terms, and presence among our known assumptions. We do not use rewriting"
  [:doc forward-chaining].
- `:linear` for a bound; give it a trigger that is a maximal term of the
  inequality [:doc linear]. Never a `:linear` rule whose conclusion is not an
  inequality: with `:trigger-terms` ACL2 admits it and SBCL faults at its first
  use (`ai/00-pitfalls-first.md`, pitfall 6); fn's version of the lesson,
  "Split it into a type rule and a plain `:linear` rule"
  [fn: docs/proof-style.md:911 @3bbfc4dca].
- `:rule-classes nil` stores the theorem and no rule [:doc rule-classes].
- `defequiv` then `defcong`: a rule whose conclusion is `(lequiv lhs rhs)`
  rewrites only where `lequiv` is maintained, which the congruence
  establishes [:doc congruence]; in the book, `(cnt (lfix (lfix x)))`
  then rewrites to `(cnt x)` with induction off
  [example: examples/shapes/rule-classes.lisp].
- The tau system can prove a goal you meant a rule to prove: in the book a
  forward-chaining demonstration had to disable `(tau-system)` as well before
  the goal was refused [example: examples/shapes/rule-classes.lisp]. Disable
  tau with `(in-theory (disable (tau-system)))` [:doc tau-system].

Book: `examples/shapes/rule-classes.lisp`.

## 3. `defthm :hints`

Each hint after a `local` `must-fail` of the hintless attempt
[example: examples/shapes/hints.lisp].

```lisp
;; :use an instance, and disable the rule it instantiates in the SAME hint
(defthm p-injective
  (implies (equal (p a) (p b)) (equal a b))
  :hints (("Goal" :use ((:instance car-p (x a))
                        (:instance car-p (x b)))
                  :in-theory (disable car-p)))
  :rule-classes nil)

;; :cases on a condition the goal does not mention
(defthm mag-non-negative
  (implies (rationalp x) (<= 0 (mag x)))
  :hints (("Goal" :cases ((< x 0)))))

;; :expand a call the rewriter will not open
(defthm len-of-tk-1
  (equal (len (tk 1 x)) 1)
  :hints (("Goal" :expand ((tk 1 x)))))

;; :induct on a term whose recursion is the induction you want
(defthm len-of-tk-succ
  (implies (natp n) (equal (len (tk (+ 1 n) x)) (+ 1 n)))
  :hints (("Goal" :induct (tk n x) :expand ((tk 1 x)))))

;; :in-theory with e/d: enable, then disable, against the current world
(defthm half-of-dbl
  (equal (half (dbl x)) (fix x))
  :hints (("Goal" :in-theory (e/d (dbl half) (mag)))))

;; a subgoal hint repeats the WHOLE theory; it does not inherit Goal's
(defthm half-of-dbl-by-cases
  (equal (half (dbl x)) (fix x))
  :hints (("Goal" :cases ((acl2-numberp x))
                  :in-theory (e/d (dbl half) (mag)))
          ("Subgoal 1" :in-theory (e/d (dbl half fix) (mag))))
  :rule-classes nil)
```

Rules:

- `:use` "replaces a goal, `G`, by the new goal, `(IMPLIES P G)`", and the new
  hypotheses "participate fully in all subsequent rewriting" [:doc hints]; an
  enabled rule rewrites its own instance to `T`. ACL2 warns "It is unusual to
  :USE the formula of an enabled :REWRITE or :DEFINITION rule"
  [:doc using-enabled-rules]. Disable it in the same hint.
- An `:in-theory` hint is evaluated "relative to the current ACL2 logical
  world, not relative to the theory of a previous goal"; "the `disable` of `f`
  on behalf of the hint at `Goal` will be lost at `Subgoal 3`" [:doc hints].
  Spell the whole `e/d` at every subgoal hint
  [fn: docs/proof-style.md:700 @3bbfc4dca].
- A goal-spec that matches no goal is ignored ("If there is no such match,
  then the hint is ignored") [:doc goal-spec]: copy the name from the output.
- `:use`, `:cases`, `:by`, `:induct` and a few others "have a specific effect
  only on the goal to which they are applied" [:doc hints].
- Prefer the general lemma to the hint: `(equal (len (tk n x)) (nfix n))`
  proves by itself and makes the `:induct` theorem need no hint
  [example: examples/shapes/hints.lisp]. "Try to avoid subgoal hints"
  [:doc best-practices].

Book: `examples/shapes/hints.lisp`.

## 4. `encapsulate`, a local witness, and `:functional-instance`

```lisp
(encapsulate
  (((step-fn *) => *))                   ; signature: one argument, one value
  (local (defun step-fn (x) (nfix x)))   ; witness: local, so not exported
  (local (defthm step-fn-witness-lemma   ; a local helper, not exported
           (natp (nfix x))))
  (defthm natp-of-step-fn                ; the constraint: exported
    (natp (step-fn x))
    :rule-classes :type-prescription))

(defun run-steps (xs)
  (if (consp xs) (+ (step-fn (car xs)) (run-steps (cdr xs))) 0))

(defthm run-steps-of-append              ; the generic theorem: one induction
  (equal (run-steps (append a b)) (+ (run-steps a) (run-steps b))))

(defun len-fn (x) (len x))
(defun run-lens (xs)
  (if (consp xs) (+ (len-fn (car xs)) (run-lens (cdr xs))) 0))

(defthm run-lens-of-append               ; the instance: no induction
  (equal (run-lens (append a b)) (+ (run-lens a) (run-lens b)))
  :hints (("Goal" :do-not-induct t
                  :use ((:functional-instance run-steps-of-append
                                              (step-fn len-fn)
                                              (run-steps run-lens))))))
```

When: a property proved once for every function meeting a constraint (loop
shapes, assumptions, a platform interface). "the local definitions of the
constrained functions are just ``witness functions'' that establish the
consistency of the constraints. Because those definitions are local, they are
not present in the theory produced by encapsulation" [:doc encapsulate].

Rules:

- The witness `defun` must be `local`; a non-local one is the second local
  incompatibility [:doc local-incompatibility]. No `defaxiom` inside
  [:doc encapsulate].
- Substitute every function whose definition mentions a constrained one
  (here `run-steps` as well as `step-fn`); the manual's example replaces the
  list functions alongside the element function
  [:doc functional-instantiation-example].
- The obligation is the constraint instantiated, proved at the hint: "the
  system will generate proof obligations arising from the replacement of the
  `fi`'s by the `gi`'s in constraints that ``support'' the lemma"
  [:doc lemma-instance].
- The book checks that the instance closes with `:do-not-induct t` and that
  the same goal without the instance is refused, so the instance is doing the
  work [example: examples/shapes/encapsulate-fi.lisp].

Book: `examples/shapes/encapsulate-fi.lisp`.

## 5. `defstobj` with array and hash-table fields

```lisp
(defconst *slots* 16)

(defstobj st
  (cnt :type (integer 0 *) :initially 0)
  (arr :type (array (unsigned-byte 8) (*slots*)) :initially 0 :resizable nil)
  (tbl :type (hash-table equal) :initially nil))
```

Generated names, for a field `c` of stobj `name` [:doc defstobj]:

| | scalar | array | hash table |
| --- | --- | --- | --- |
| recognizer | `(cP x)` | `(cP x)` | `(cP x)` |
| accessor | `(c name)` | `(cI i name)` | `(c-get k name)` |
| updater | `(UPDATE-c v name)` | `(UPDATE-cI i v name)` | `(c-put k v name)` |
| other | | `(c-LENGTH name)`, `(RESIZE-c i name)` | `c-boundp`, `c-get?`, `c-rem`, `c-count`, `c-clear`, `c-init` |

A hash-table field "is logically an association list, initially empty,
accessed using function `hons-assoc-equal`" [:doc defstobj]. For it,
`:initially` "specifies a default rather than an initial value"
[:doc defstobj].

The theorems an includer needs, proved once, in accessor vocabulary:

```lisp
(defthm arrp-nth-natp
  (implies (and (arrp l) (natp i) (< i (len l))) (natp (nth i l)))
  :rule-classes :type-prescription)
(defthm arrp-nth-bound
  (implies (and (arrp l) (natp i) (< i (len l))) (< (nth i l) 256))
  :rule-classes :linear)
(defthm arrp-of-update-nth
  (implies (and (arrp l) (natp i) (< i (len l)) (unsigned-byte-p 8 v))
           (arrp (update-nth i v l))))

(defthm arri-of-update-arri-same
  (equal (arri i (update-arri i v st)) v))
(defthm arri-of-update-arri-diff
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (arri i (update-arri j v st)) (arri i st))))
(defthm tbl-get-of-tbl-put-same
  (equal (tbl-get k (tbl-put k v st)) v))
(defthm stp-of-put-byte
  (implies (and (stp st) (natp i) (< i *slots*) (unsigned-byte-p 8 v))
           (stp (put-byte i v st))))
```

Rules:

- The three `arrp` lemmas are over `nth`/`update-nth` because that is what the
  recognizer opens into; without them `stp-of-put-byte` is refused
  [measured: examples/shapes/stobj-fields.lisp with the three lemmas removed,
  laptop REPL, ACL2 8.7 / SBCL 2.6.8].
- `:resizable nil` still defines the field's resizer (`RESIZE-c`), guard-
  verified and logically the identity; executing it is a hard error
  [example: examples/performance/bounded-table.lisp].
- Close the writers (`in-theory (disable ...)`) after the read-over-write
  lemmas, so includers reason in accessor vocabulary
  [example: examples/shapes/stobj-fields.lisp].

Book: `examples/shapes/stobj-fields.lisp`.

## 6. `with-local-stobj` and `mv`

```lisp
(defun total-and-scratch (xs scratch)
  (declare (xargs :stobjs scratch :guard (nat-listp xs)))
  (let ((scratch (add-all xs scratch)))
    (mv (acc scratch) scratch)))

(defun total (xs)
  (declare (xargs :guard (nat-listp xs)))
  (with-local-stobj scratch
    (mv-let (sum scratch)
      (total-and-scratch xs scratch)
      sum)))
```

The obligation, quoted: `mv-let-form` "is a call of `mv-let` that binds
`stobj-name` but does not return `stobj-name` -- in fact, if `mv-let-form` is
`(mv-let (...) ... body)`, then `body` does not even reference `stobj-name`"
[:doc with-local-stobj]. The wrong shapes and what ACL2 prints for each
[example: examples/shapes/local-stobj.lisp]:

| wrong | ACL2 says |
| --- | --- |
| body returns the stobj: `(mv sum scratch)` | "Contrary to the declaration that it is IGNOREd, the variable SCRATCH is used in the MV-LET expression" |
| stobj argument is a call: `(f xs (update-acc 0 scratch))` | "the variable SCRATCH is required, not merely a term that returns such a single-threaded object, so you may need to bind SCRATCH with LET" |
| `mv-let` binds three names to a two-valued call | "The bound variable list (SUM EXTRA SCRATCH) from an MV-LET expression has been found not to be compatible with the ``types'' ... (NIL SCRATCH)" |
| a two-valued call as an argument: `(car (pair-up x))` | "It is illegal to invoke PAIR-UP here because of a signature mismatch. This function call returns a result of shape (MV * *) where a result of shape * is required." |

Fixes: return the other values only; `(let ((scratch (update-acc 0 scratch)))
(f xs scratch))`; bind exactly the callee's values; take one value with
`mv-let`, or with `(mv-list 2 (pair-up x))` in an `assert-event`, and write
`(mv-nth 1 (pair-up x))` in theorems [example: examples/shapes/local-stobj.lisp].
fn's lane recorded the first two after paying for them
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:26 @worktree].

- `:non-executable t` on a stobj used only this way "avoids actually creating
  a global stobj" [:doc defstobj].
- `with-local-stobj` creates the stobj per call: its expansion is
  `(let ((st (create-st))) ...)` [:doc with-local-stobj]; keep it out of
  loops (chapter 5 measured 16 KiB a call for a 2,048-word stobj,
  [example: examples/performance/time-list-vs-stobj.lisp]).
- It is not legal typed at the top level [:doc with-local-stobj]; wrap it in a
  `defun` and call that.

Book: `examples/shapes/local-stobj.lisp`.

## 7. `stobj-let` (a stobj inside a stobj)

```lisp
(defstobj kid (n :type (integer 0 *) :initially 0))
(defstobj par
  (k :type kid)
  (ops :type (integer 0 *) :initially 0))

(defun par-bump (par)                     ; write the child, update the parent
  (declare (xargs :stobjs par))
  (stobj-let
   ((kid (k par)))                        ; bindings
   (kid)                                  ; producer variables
   (update-n (+ 1 (n kid)) kid)           ; producer
   (update-ops (+ 1 (ops par)) par)))     ; consumer

(defun par-n (par)                        ; read a child field into a value
  (declare (xargs :stobjs par))
  (stobj-let
   ((kid (k par)))
   (v)
   (n kid)
   v))
```

- ACL2 "disallows direct calls of stobj accessors and updaters for fields
  whose `:type` is a stobj"; `stobj-let` is the way [:doc nested-stobjs].
  The refusal of `(n (k par))` says "you may need to bind KID with LET"; for a
  child stobj the binding form is `stobj-let`
  [example: examples/shapes/stobj-let.lisp].
- "`ST` must not occur free in `PRODUCER` when at least one variable in
  `STOBJ-LET-BOUND-VARIABLES` occurs in `PRODUCER`; and every variable in
  `STOBJ-LET-BOUND-VARIABLES` must not occur free in `CONSUMER`"
  [:doc nested-stobjs].
- A `stobj-let` "cannot be evaluated directly in the top-level loop"
  [:doc nested-stobjs].
- Two children of one array at once need a congruent stobj and distinct
  indices [:doc nested-stobjs].

Book: `examples/shapes/stobj-let.lisp`.

## 8. `defabsstobj` with every obligation

```lisp
(defstobj ctr$c
  (val :type (integer 0 *) :initially 0)
  (lim :type (integer 0 *) :initially 100))

(defun ctr$ap (x) (declare (xargs :guard t)) (and (natp x) (<= x 100)))
(defun create-ctr$a () (declare (xargs :guard t)) 0)
(defun ctr-get$a (x) (declare (xargs :guard (ctr$ap x))) x)
(defun ctr-incr$a (x)
  (declare (xargs :guard (ctr$ap x)))
  (if (< x 100) (+ 1 x) x))
(defun ctr-add$a (k x)
  (declare (xargs :guard (and (natp k) (ctr$ap x) (<= (+ k (ctr-get$a x)) 100))))
  (+ k x))

(defun incr$c (ctr$c)
  (declare (xargs :stobjs ctr$c))
  (if (< (val ctr$c) (lim ctr$c)) (update-val (+ 1 (val ctr$c)) ctr$c) ctr$c))
(defun add$c (k ctr$c)
  (declare (xargs :stobjs ctr$c
                  :guard (and (natp k) (<= (+ k (val ctr$c)) (lim ctr$c)))))
  (update-val (+ k (val ctr$c)) ctr$c))

(defun-nx ctr$corr (ctr$c x)
  (and (ctr$cp ctr$c) (equal (lim ctr$c) 100) (equal (val ctr$c) x)))

;; the obligations, under the names ACL2 prints (all :rule-classes nil)
(defthm create-ctr{correspondence} (ctr$corr (create-ctr$c) (create-ctr$a))
  :rule-classes nil)
(defthm create-ctr{preserved} (ctr$ap (create-ctr$a)) :rule-classes nil)
(defthm ctr-get{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (equal (val ctr$c) (ctr-get$a ctr)))
  :rule-classes nil)
(defthm ctr-incr{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (ctr$corr (incr$c ctr$c) (ctr-incr$a ctr)))
  :rule-classes nil)
(defthm ctr-incr{preserved}
  (implies (ctr$ap ctr) (ctr$ap (ctr-incr$a ctr)))
  :rule-classes nil)
(defthm ctr-add{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (natp k) (ctr$ap ctr)
                (<= (+ k (ctr-get$a ctr)) 100))
           (ctr$corr (add$c k ctr$c) (ctr-add$a k ctr)))
  :rule-classes nil)
(defthm ctr-add{guard-thm}
  (implies (and (ctr$corr ctr$c ctr) (natp k) (ctr$ap ctr)
                (<= (+ k (ctr-get$a ctr)) 100))
           (and (natp k) (<= (+ k (val ctr$c)) (lim ctr$c))))
  :rule-classes nil)
(defthm ctr-add{preserved}
  (implies (and (natp k) (ctr$ap ctr) (<= (+ k (ctr-get$a ctr)) 100))
           (ctr$ap (ctr-add$a k ctr)))
  :rule-classes nil)

(defabsstobj ctr
  :exports ((ctr-get :logic ctr-get$a :exec val)
            (ctr-incr :logic ctr-incr$a :exec incr$c)
            (ctr-add :logic ctr-add$a :exec add$c)))
```

How to get the obligations right: define the `:logic` and `:exec` functions,
submit the `defabsstobj`, and copy what it prints. "Although the `defabsstobj`
event will fail if the required lemmas have not been proved, first it will
print the `defthm` forms that must be admitted" [:doc defabsstobj]; the book
keeps that first submission as a `local` `must-fail`
[example: examples/shapes/absstobj.lisp]. `defabsstobj-missing-events` returns
the same formulas as data [:doc defabsstobj-missing-events].

The three kinds: `{CORRESPONDENCE}` (logic and exec agree under the
correspondence), `{PRESERVED}` (an updater keeps the abstract recognizer,
only "if and only if the specified `:EXEC` function returns the foundational
stobj"), `{GUARD-THM}` ("if the `:LOGIC` function's guard holds, then the
`:EXEC` function's guard holds") [:doc defabsstobj].

Refusals met while writing the book [example: examples/shapes/absstobj.lisp]:

- An export named `get`: "Symbols in the main Lisp package, such as GET, may
  not be defined or constrained."
- `(<= (+ k x) 100)` in `ctr-add$a`'s guard: "A single-threaded object, namely
  CTR, is being used where an ordinary object is expected." An export's guard
  is the `:logic` guard with each `:logic` function replaced by its export,
  and it "must return a single non-stobj value and satisfy normal syntactic
  restrictions, including single-threadedness" [:doc defabsstobj]. Read the
  abstract value through a `:logic` reader (`ctr-get$a`).
- After editing a `:logic` guard, the previously proved obligations no longer
  match: ACL2 prints "Note discrepancy with existing formula named
  CTR-ADD{CORRESPONDENCE}". Restate them from the new printout.
- Every `:logic` and `:exec` function "must be guard-verified"
  [:doc defabsstobj].

Book: `examples/shapes/absstobj.lisp`.

## 9. `mbe`: the loop twin

```lisp
(defun sum-to (n)                          ; :logic, what theorems are about
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (+ n (sum-to (- n 1)))))

(defun sum-to-loop (n acc)                 ; :exec, what runs
  (declare (xargs :guard (and (natp n) (natp acc))))
  (if (zp n) acc (sum-to-loop (- n 1) (+ n acc))))

(defthm sum-to-loop-is-sum-to              ; the bridge, general in ACC
  (implies (natp acc)
           (equal (sum-to-loop n acc) (+ acc (sum-to n))))
  :rule-classes nil)

(defun sum-to-fast (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :use ((:instance sum-to-loop-is-sum-to
                                                         (acc 0)))))))
  (mbe :logic (sum-to n)
       :exec (sum-to-loop n 0)))
```

- The guard obligations of an `mbe` include "the term `(equal exec-code
  logic-code)`" [:doc mbe]; the bridge discharges it. The book shows the same
  `defun` refused without it [example: examples/shapes/mbe-memoize.lisp].
- Only `:exec` runs, and only "in the body of a guard-verified function or
  under a call of a `:program` mode function"; elsewhere `:logic` runs
  [:doc mbe]. Assert `:common-lisp-compliant`.
- State the bridge for every accumulator, not for `0`: the special case does
  not induct [example: examples/prover/induction-accumulator.lisp].

Book: `examples/shapes/mbe-memoize.lisp`.

## 10. `memoize`

```lisp
(defun fib (n)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (= n 1)) 1 (+ (fib (- n 1)) (fib (- n 2)))))

(memoize 'fib)
(assert-event (equal (fib 80) 37889062373143906))
```

- "only the corresponding raw Lisp function is actually memoized, so guard
  violations can defeat memoization, and `:logic` mode functions without their
  guards verified will only be memoized when called by `:program` mode
  functions" [:doc memoize]. Verify the guards first.
- `(memoize 'fn :condition '(test x))` memoizes only when the condition holds
  [:doc memoize]; `(profile 'fn)` is `memoize` for counting, read with
  `(memsum)` [:doc profile].

Book: `examples/shapes/mbe-memoize.lisp`.

## 11. `make-event`, `assert-event`, `must-fail`: the teeth of a keystone

```lisp
(defmacro clamp-hyps (lo hi) `(<= ,lo ,hi))
(defmacro clamp-concl (x lo hi)
  `(and (<= ,lo (clamp ,x ,lo ,hi)) (<= (clamp ,x ,lo ,hi) ,hi)))

(assert-event (let ((x 9) (lo 1) (hi 5))            ; satisfiable, and fires
                (and (clamp-hyps lo hi)
                     (equal (clamp x lo hi) 5)
                     (clamp-concl x lo hi))))

(assert-event (let ((x 3) (lo 5) (hi 1))            ; the hypothesis has teeth
                (and (not (clamp-hyps lo hi))
                     (not (clamp-concl x lo hi)))))

(defthm clamp-within-bounds                          ; the keystone
  (implies (clamp-hyps lo hi) (clamp-concl x lo hi)))

(assert-event (let ((x 9) (lo 1) (hi 5))            ; a mutant, refuted by a value
                (and (clamp-hyps lo hi)
                     (not (< (clamp x lo hi) hi)))))

; teeth: prover-refusal  (beside the value above, never instead of it)
(local
 (must-fail
  (defthm clamp-strictly-below-mutant
    (implies (clamp-hyps lo hi) (< (clamp x lo hi) hi)))))

(make-event                                          ; refuse to certify unless
 (if (equal (clamp 9 1 5) 5)                         ; a check holds
     '(value-triple :clamp-check-ok)
   (er hard 'teeth "clamp check failed")))
```

- Write the statement once (the two macros) so witnesses evaluate the term the
  theorem states [example: examples/process/statement-first.lisp].
- A hypothesis with no violating value is unnecessary: delete it. The book's
  keystone has no `rationalp` hypotheses for that reason
  [example: examples/shapes/teeth.lisp]; fn's rule: "If no violating value
  exists for a hypothesis, the hypothesis is unnecessary: delete it"
  [fn: docs/proof-style.md:384 @3bbfc4dca].
- "Never a general negated `must-fail`: it proves that the prover could not
  find a proof, which is not a counterexample, and it loops when the negation
  is unprovable rather than false" [fn: docs/proof-style.md:381 @3bbfc4dca].
- `must-fail` by default counts only soft errors; `:expected :hard` or `:any`
  widen it [books: std/testing/must-fail.lisp:17].
- `assert-event` is skipped when proofs are skipped (during `include-book`)
  unless given `:on-skip-proofs t` [:doc assert-event].
- `make-event`'s expansion "is recorded in the book's certificate and re-used
  during a subsequent `include-book`" [:doc make-event].
- An `assert-event` cannot evaluate a multiple-value call in an argument
  position; wrap it in `mv-list` (section 6).

Book: `examples/shapes/teeth.lisp`.

## 12. Step and time limits around an event

```lisp
(local
 (must-fail
  (with-prover-step-limit 20
    (defthm app-assoc-probe
      (equal (app (app x y) z) (app x (app y z)))))))

(with-prover-time-limit 30
  (defthm app-assoc
    (equal (app (app x y) z) (app x (app y z)))))
```

- A stopped probe "says the form did not finish inside `n`; it says nothing
  about whether the form closes" [fn: docs/proof-style.md:650 @3bbfc4dca]. A
  `yes` under a limit is evidence; a `no` is not.
- Time limits are CPU time by default; inner limits cannot extend an outer one
  unless written as a list, `'(30)` [:doc with-prover-time-limit].

Book: `examples/process/step-limit-probe.lisp` (chapter 6's).

## 13. `include-book`: `:dir :system`, a `local` include, a sibling

```lisp
(include-book "std/lists/rev" :dir :system)            ; exported to includers
(local (include-book "std/lists/take" :dir :system))   ; private to this book
(include-book "teeth")                                  ; a sibling, relative

(defthm len-of-take-of-rev                             ; uses the local rules
  (implies (natp n) (equal (len (take n (rev x))) n)))

(in-theory (disable len-of-take-of-rev))               ; the export event, last
```

What an includer gets, checked in `examples/shapes/includes-user.lisp`:

```lisp
(include-book "includes")
(assert-event (getpropc 'rev-of-append 'theorem nil (w state)))     ; present
(assert-event (not (getpropc 'len-of-take 'theorem nil (w state)))) ; absent
(assert-event (equal (disabledp 'len-of-take-of-rev)
                     '((:rewrite len-of-take-of-rev))))
```

- `local` events "are processed when the encapsulation or book is checked for
  admissibility in `:logic` mode but are skipped when extending the host
  world" [:doc local]. A lemma your dependent needs must be non-local in some
  book it includes; the includer's `must-fail` shows the goal the local rule
  closed is no longer closed by rewriting
  [example: examples/shapes/includes-user.lisp].
- "`include-book` and `in-theory` events should be local where possible"
  [:doc best-practices]. A non-local include of a book that ends with no
  theory withdrawal is not an interface: fn measured one turning "a six-minute
  proof into an 1800 s timeout" [fn: docs/proofs.md:257 @3bbfc4dca].
- Enable an exported-but-disabled rule in the one hint that needs it
  [fn: docs/proof-style.md:747 @3bbfc4dca].

Books: `examples/shapes/includes.lisp`, `examples/shapes/includes-user.lisp`.

## 14. The `.acl2` portcullis with `defpkg`

`examples/shapes/pkg-book.acl2`:

```lisp
(in-package "ACL2")
(defpkg "SHAPES"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
```

`examples/shapes/pkg-book.lisp`:

```lisp
(in-package "SHAPES")

(defun double (x) (* 2 (fix x)))

(defthm double-of-double
  (equal (double (double x)) (* 4 (fix x))))
```

- `defpkg` forms "should not occur in books" [:doc defpkg]. `cert.pl` finds
  them in `foo.acl2` for `foo.lisp`, else in the directory's `cert.acl2`
  [books: build/doc.lisp:558]; the `defpkg` becomes part of the
  certificate's portcullis, which the certificate of `pkg-book` shows
  [measured: `grep -c SHAPES examples/shapes/pkg-book.cert` after
  `examples/certify.sh shapes/pkg-book.lisp`, laptop, ACL2 8.7 / SBCL 2.6.8].
- A package name has no lower-case characters [:doc defpkg].
- For many books sharing a package, the community recipe is a `package.lsp`
  loaded by a portcullis book, so certificates share one redundant include
  [:doc working-with-packages].

Book: `examples/shapes/pkg-book.lisp` with `pkg-book.acl2`.

## 15. `cert.pl` invocation

```sh
cd <repo> && examples/certify.sh shapes/hints.lisp
# which runs, under a machine-wide lock:
perl "$ACL2_SYSTEM_BOOKS/build/cert.pl" --acl2 "$ACL2" shapes/hints.lisp
```

Success prints one line per book:

```
Built ~/dev/acl2aiguide/examples/shapes/hints.cert (0.514s) at 28-Oct-2026 02:19:16.395
```

[measured: `examples/certify.sh shapes/hints.lisp`, laptop, ACL2 8.7 / SBCL
2.6.8]. Failure prints `**CERTIFICATION FAILED** for <book>` and leaves no
`.cert`; read the book's `.cert.out` from its first `ACL2 Error`. That log's
last lines in one failed run were `Exit code from ACL2 is 0` and
`includes-user.cert seems to be missing`, and in a successful one `Exit code
from ACL2 is 43` [measured: the first and the final certification of
examples/shapes/includes-user.lisp and of examples/shapes/hints.lisp, their
`.cert.out`]: the verdict is the certificate and the `**CERTIFICATION
FAILED**` line, not ACL2's exit code; fn's version: "a book that failed still
exits 0" [fn: docs/proofs.md:607 @3bbfc4dca].

- `cert.pl` "will rebuild exactly the necessary books, in parallel"
  [books: build/doc.lisp:34]; `-j N` parallelism (memory bounds it), `-k` keep
  going, `-p` dependencies only [books: build/doc.lisp:297].
- Its dependency scanner is "a dumb Perl script": an `include-book` with the
  book name on the next line is invisible to it [books: build/doc.lisp:297].
- The default certify command is `(certify-book "foo" ? t)`, which refuses
  `skip-proofs`, `defaxiom` and trust tags unless the book's `cert-flags` say
  otherwise [books: build/doc.lisp:673].

## 16. A driver `.lsp` for the REPL

`examples/shapes/driver.lsp`, run as
`timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < driver.lsp > driver.out 2>&1`
from `examples/shapes`:

```lisp
(set-gag-mode :goals)                        ; key checkpoints and goal names only
(set-inhibit-output-lst '(proof-tree))       ; drop proof-tree output
(include-book "hints")                       ; certified closure: seconds, no proofs

(ld '((defthm mag-of-mag
        (implies (rationalp x) (equal (mag (mag x)) (mag x)))
        :hints (("Goal" :cases ((< x 0)))))
      (defthm mag-is-zero-only-at-zero
        (implies (equal (mag x) 0) (equal x 0)))
      (defthm mag-of-neg
        (implies (rationalp x) (equal (mag (- x)) (mag x)))
        :hints (("Goal" :cases ((< x 0))))))
    :ld-pre-eval-print t
    :ld-error-action :continue)

(with-prover-time-limit 10
  (defthm len-of-tk-2 (equal (len (tk 2 x)) 2)))

:pe mag-non-negative
:pl (mag x)
:pr mag-when-negative

:brr t
:monitor (:rewrite mag-when-negative) t
(thm (implies (and (rationalp y) (< y 0)) (equal (mag y) (- y))))
:target
:eval
:go
:unmonitor (:rewrite mag-when-negative)
:brr nil
(quit)
```

What one run of it printed [measured: the command above, laptop, ACL2 8.7 /
SBCL 2.6.8]:

- the three batched `defthm`s each printed before running; the first proved;
  the second was refused ("A :REWRITE rule generated from
  MAG-IS-ZERO-ONLY-AT-ZERO is illegal because it rewrites the variable symbol
  X"); the third failed at a key checkpoint; the run went on;
- `:pe` printed the event with its include-book command; `:pl (mag x)` listed
  both rewrite rules, the disabled definition and the type prescription;
  `:pr` printed the rule's `Hyps`, `Lhs`, `Rhs`;
- the monitored rule broke with `(1 Breaking (:REWRITE MAG-WHEN-NEGATIVE) on
  (MAG Y):`, `:target` printed `(MAG Y)`, `:eval` printed `1! (:REWRITE
  MAG-WHEN-NEGATIVE) produced (UNARY-- Y).`, and `:go` finished the proof.

Rules:

- `ld` on a list of forms or a file stops at the first error unless told
  otherwise: "the default value for `ld-error-action` on calls of `ld` is
  `:return!`", and `:continue` "just continues processing the forms"
  [:doc ld-error-action]. The top-level loop itself continues
  (its initial value is `:continue`) [:doc ld-error-action].
- `:ld-pre-eval-print t` prints each form before evaluating it, "useful if you
  are reading from a file of commands" [:doc ld-pre-eval-print].
- `(set-gag-mode :goals)` is the default: key checkpoints, and goal names as
  they are generated [:doc set-gag-mode]; `(set-gag-mode nil)` prints the
  whole narration.
- `(set-inhibit-output-lst lst)` drops kinds of output (`prove`, `event`,
  `summary`, `warning`, `proof-tree`, ...); hard errors stay unless you
  `(assign inhibit-er-hard t)` [:doc set-inhibit-output-lst].
- Break-rewrite commands are read from the same input as everything else,
  so a driver can answer a break; `:a!` aborts one [:doc break-rewrite].
- A changed definition is refused, not replaced: "The name F1 is in use as a
  function ... The redefinition feature is currently off", and the old body
  stays (`(f1 3)` still returned the old answer) [measured: `(defun f1 (x) (+
  x 1))` then `(defun f1 (x) (+ x 2))` then `(f1 3)`, laptop REPL]. An
  identical resubmission is ":REDUNDANT". After editing a book, start a new
  session or `:ubt` back past the changed event [:doc ubt],
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:24 @worktree].

## 17. `:doc` and the history commands

```
:doc with-local-stobj       ; the manual, rendered (strip colour codes)
:args f                     ; formals, guard, signature, type, badge
:pe f                       ; the event that introduced f
:pl (f x)                   ; rules that could rewrite this term
:pr name                    ; the rules an event stored, with enabled status
:pc f / :pbt 1 / :ubt f     ; one command / commands back to one / undo them
```

`ai/02-reading-the-manual.md` has the shell recipe for the manual and each
command's source.

## 18. Index of the shape books

| book | shapes |
| --- | --- |
| `examples/shapes/defun-guards.lisp` | `:guard`, `:measure`, `:verify-guards nil`, `verify-guards`, `:guard-hints`, `symbol-class` |
| `examples/shapes/rule-classes.lisp` | every everyday rule class |
| `examples/shapes/hints.lisp` | `:use`/`:instance`, `:cases`, `:expand`, `:induct`, `:in-theory (e/d ...)`, subgoal hints |
| `examples/shapes/encapsulate-fi.lisp` | `encapsulate`, local witness, `:functional-instance` |
| `examples/shapes/stobj-fields.lisp` | `defstobj` scalar/array/hash-table fields, read-over-write theorems |
| `examples/shapes/local-stobj.lisp` | `with-local-stobj`, `mv`, `mv-let`, `mv-list`, four refused shapes |
| `examples/shapes/stobj-let.lisp` | nested stobj, `stobj-let` write and read |
| `examples/shapes/absstobj.lisp` | `defabsstobj` with CORRESPONDENCE, PRESERVED, GUARD-THM |
| `examples/shapes/mbe-memoize.lisp` | `mbe` loop twin with its bridge, `memoize` |
| `examples/shapes/teeth.lisp` | witnesses, teeth, mutant, `make-event` checks |
| `examples/shapes/includes.lisp`, `includes-user.lisp` | `include-book` `:dir :system`, `local` include, export event |
| `examples/shapes/pkg-book.lisp`, `pkg-book.acl2` | `defpkg` in the portcullis |
| `examples/shapes/driver.lsp` | the REPL driver (not a book) |
