# ai/03. The prover: failed proofs, hints, rules, theories, books

Load after `ai/00-pitfalls-first.md`, `ai/01-form-shapes.md` and
`ai/02-reading-the-manual.md`. This is the terse twin of
`humans/01-logic-and-prover.md` and `humans/02-rewriting-theories-books.md`;
read those for the why. Every form below is copied from a certified book under
`examples/`. Citations: `[:doc X]` is the ACL2 8.7 manual topic X; `[fn: P:L
@3bbfc4dca]` is fn at `origin/dev`; `[measured: ...]` is the laptop REPL (ACL2
8.7, SBCL 2.6.8) on the forms named; `[example: P]` is a certified book here.

## 0. Pitfalls, in the order you meet them

| symptom | cause | go to |
| --- | --- | --- |
| checkpoint after induction is false on small values | the conjecture is false | 2.3 |
| induction hyp is about `acc = NIL`, goal about `(LIST (CAR X))` | statement too specific | 2.4 |
| prover inducts, fails in `*1.1`, `*1.1.2` | a lemma is missing, not an induction | 2.4 |
| `No induction schemes are suggested` | non-variable controlling args, or mutual recursion | 4 |
| `:use` did nothing; `[Use]` warning; `(:REWRITE LEMMA)` in `Rules:` | the lemma is an enabled rule and rewrote its own instance to `T` | 3.1 |
| a `Goal` `:in-theory` stopped holding below | a subgoal hint with its own `:in-theory` | 3.5 |
| `HARD ACL2 ERROR [Call depth]`, or the prover goes silent | rewrite loop or case explosion | 6.5 |
| `ACL2 Error [Step-limit]` read as "false" or "slower" | an aborted probe measures nothing | 5 |
| `Time:` shows `prove: 0.02 ... other: 2386.24` | forward chaining / type reasoning, not the rewriter | 2.6 |
| a proved rule never fires | free variable, non-recursive hyp already opened, wrong normal form | 6 |
| an includer's proofs got slow | a book exported its internals | 8.5 |
| a `must-fail` read as a counterexample | it is only the prover's refusal | 9.6 |

## 1. The logic, in five rules

- Total, untyped, first-order. Every function is defined on every object; `(+ t
  3)` is `3` [:doc |About Types|]. A conjecture is about all objects, not the
  ones you meant [:doc frequently-asked-questions-by-newcomers].
- A guard is not a hypothesis: "the guard of `fn` has no bearing on this logical
  axiom" [:doc defun]. State what a theorem needs in its hypotheses
  (`ai/04-modelling.md` section 2).
- `:program` functions have no axioms and cannot appear in theorems; `:logic`
  functions call only `:logic` functions [:doc defun-mode]. In a book write
  `(program)` / `(logic)`, never the keyword commands [:doc program], [:doc logic].
- Admission proves `(o-p (m x))` and `o<` decrease under the *rulers*: the tests
  of the top-level `IF` structure only. A test under `cons` or a `let` does not
  rule; lift it, or `(declare (xargs :ruler-extenders (cons)))` /
  `(:lambdas)` / `:all` (names functions, not macros: `binary-+`) [:doc rulers].
- Mutual recursion suggests no induction; you must supply it (section 4.3)
  [:doc frequently-asked-questions-by-newcomers].

## 2. Reading a failed proof

### 2.1 Where to look

- Default output is gag mode `:goals`; key checkpoints print between `([` and
  `])` and again after "The key checkpoint goals, below, may help you to debug
  this failure" [:doc set-gag-mode], [:doc introduction-to-the-theorem-prover].
- Full narration: `(set-gag-mode nil)`; after the fact: `:pso`, or `(pso
  "Subgoal *1/2''")` for one goal [:doc set-gag-mode], [:doc pso].
- Do not analyse failed sub-inductions (`*1.1...`); analyse the key checkpoint
  that pushed them: "the ``higher level'' the checkpoint, the more worthy it is
  of attention" [:doc set-gag-mode].
- `:otf-flg t` keeps all pushed subgoals instead of "we prefer in this instance
  to focus on the original input conjecture" [:doc otf-flg].

### 2.2 The order of questions (The Method, condensed)

1. Is the checkpoint a theorem? Evaluate it on small constants (2.3).
2. Can a simpler fact about a few function symbols simplify it? Prove that as
   a rule (2.4).
3. Is that fact already a rule? Then why did it not fire: disabled; left side
   does not match; `IFF` rule not in a propositional position; hypotheses
   not relievable [:doc introduction-to-key-checkpoints].
4. Is it an induction goal, general enough? Did ACL2 induct, on the right
   scheme?
5. After any repair, resubmit the main conjecture; do not scroll back
   [:doc introduction-to-key-checkpoints].
Read from the start, not the end: find the first place the proof deviates
from the one you imagined [:doc the-method].

### 2.3 The goal is false

Pitfall: you analyse checkpoints of a false conjecture. "If you see a
post-induction key checkpoint that is not a theorem, stop looking at the
checkpoints! Your original conjecture is not a theorem!"
[:doc post-induction-key-checkpoints]. This holds for simplification
checkpoints too, never after generalization or elimination of irrelevance
[:doc the-method]. It prints like:

```
Subgoal 8'
(IMPLIES (AND (INTEGERP N)
              (<= 0 N)
              (NOT (INTEGERP M)))
         (NOT (TK N NIL)))
```

[measured: the first `thm` of examples/prover/false-conjecture.lisp]. Shape:
evaluate first, then state the corrected theorem
[example: examples/prover/false-conjecture.lisp]:

```lisp
(assert-event (equal (tk 2 (tk 0 '(a b))) '(nil nil)))
(assert-event (not (equal (tk 2 (tk 0 '(a b)))
                          (tk (min 2 0) '(a b)))))

(defthm tk-of-tk-when-not-longer
  (implies (and (natp n) (natp m) (<= n m))
           (equal (tk n (tk m x))
                  (tk n x))))
```

Rule: before reading any checkpoint, evaluate the conjecture on the non-list,
zero and short-list cases totality admits.

### 2.4 Too specific, or a lemma missing

Too specific: the induction hypothesis is about the constant you wrote.

```
Subgoal *1/1'
(IMPLIES (AND (CONSP X)
              (EQUAL (RVA (CDR X) NIL) (RV (CDR X))))
         (EQUAL (RVA (CDR X) (LIST (CAR X)))
                (APPEND (RV (CDR X)) (LIST (CAR X)))))
```

[measured: `(thm (equal (rva x nil) (rv x)))`, examples/prover/induction-accumulator.lisp].
Prove the statement for every accumulator; the special case follows by
rewriting [example: examples/prover/induction-accumulator.lisp]:

```lisp
(defthm rva-is-rv-append
  (equal (rva x acc)
         (append (rv x) acc)))
```

Missing lemma: ACL2 picks a plausible induction and fails in sub-inductions;
the database lacks a simplifying fact. With it, `drop-commutes` needs no
induction [example: examples/prover/induction-lemma-first.lisp]:

```lisp
(defthm drop-of-drop
  (implies (and (natp i) (natp j))
           (equal (drop i (drop j x))
                  (drop (+ i j) x))))
```

Ask "can a simpler fact simplify this?" before "is it general enough to
induct?" [:doc introduction-to-key-checkpoints].

### 2.5 What else to look for in a clause

- A checkpoint is a clause after rewriting: `(natp n)` arrives as `(INTEGERP N)
  (<= 0 N)` [measured: the first `thm` of examples/prover/induct-hint.lisp].
  Your rules must match the normal form, not what you typed.
- Contradictory hypotheses: `(P (F A))` with `(NOT (Q (G (F A))))` means a lemma
  `(implies (p x) (q (g x)))` is missing [:doc the-method].
- `HIDE`: ignored by the rewriter. From a failed ground evaluation of a
  constrained function (`(hide (comment "Failed attempt to call constrained
  function ..." ...))`), `:expand` does not help; disable the executable
  counterpart [:doc hide]. Otherwise open with `:expand ((:free (x) (hide x)))`
  [:doc hide].
- `Splitter note ... if-intro: ((:DEFINITION NFIX))` names the rule that split
  the goal [:doc splitter].

### 2.6 The summary: read `Time:` before the subgoals

Fields: `Form`, `Rules`, `Hint-events`, `Splitter-rules`, `Warnings`, `Time`,
`Prover steps counted` [:doc summary].

- `prove` near zero and `other` large is not the rewriter: "`other` is where
  forward chaining and type reasoning go"; the cure is "a **theory change, not
  a hint**" [fn: docs/proof-style.md:591-605 @3bbfc4dca]. fn's case:

  ```
  Time:  2386.26 seconds (prove: 0.02, print: 0.00, other: 2386.24)
  ```

  was a second whole-state recognizer exported with its own rule family,
  doubling the forward-chaining work [fn: docs/proof-style.md:607 @3bbfc4dca].
- `prove` large and steps few: the tau system or a library's
  `syntaxp`/`bind-free` tests, which count no steps and show no frames. Test by
  `(in-theory (disable (tau-system)))` after the includes and compare
  [fn: docs/proof-style.md:621 @3bbfc4dca].
- A step is "each call of the system functions `rewrite` and
  `expand-abbreviations`" [:doc set-prover-step-limit]. Steps, not seconds, are
  the regression ratchet: "for fixed bytes and toolchain the count is the same
  on any box at any load" [fn: docs/proofs.md:117 @3bbfc4dca].

## 3. Hints

General form: `:hints (("Goal" :key val ...) ("Subgoal 2" ...))`. Copy the
goal name from the output; an unmatched name "is ignored"
[:doc goal-spec]. `:hints` in `xargs` is for termination, `:guard-hints` for
guards [:doc hints]. Not inherited by subgoals: `:bdd :by :cases
:clause-processor :error :induct :or :use` [:doc hints]. `:use` and `:induct`
together are illegal [:doc hints]. Prefer a lemma to a subgoal hint: "Try to
avoid subgoal hints" [:doc best-practices].

### 3.1 `:use` and `:instance`

Pitfall: `:use` adds the instance as a hypothesis, which "participate[s] fully
in all subsequent rewriting" [:doc hints]; an enabled rewrite rule rewrites it
to `T`. It prints:

```
ACL2 Warning [Use] in ( THM ...):  It is unusual to :USE the formula
of an enabled :REWRITE or :DEFINITION rule, so you may want to consider
disabling (:REWRITE CAR-P) in the hint provided for Goal.  See :DOC
using-enabled-rules.
```

[measured: the failing `thm` of examples/prover/use-instance.lisp]. Shape:
disable the rule in the same hint [example: examples/prover/use-instance.lisp]:

```lisp
(defthm p-injective
  (implies (equal (p x1) (p x2))
           (equal x1 x2))
  :hints (("Goal" :use ((:instance car-p (x x1))
                        (:instance car-p (x x2)))
                  :in-theory (disable car-p)))
  :rule-classes nil)
```

Better: store a fact meant only for `:use` with `:rule-classes nil`, so it
changes no other proof [example: examples/prover/rule-classes-nil-use.lisp]:

```lisp
(defthm mag-bound
  (implies (rationalp x) (<= 0 (mag x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mag))))

(defthm twice-mag-non-negative
  (implies (rationalp y) (<= 0 (+ (mag y) (mag y))))
  :hints (("Goal" :use ((:instance mag-bound (x y))))))
```

fn's rule: "An equality that exists to discharge a guard or an `mbe`
obligation is not a rewrite rule. It is stated once, `:rule-classes nil`, and
used by `:use`" [fn: docs/proof-style.md:242 @3bbfc4dca]. Lemma instances: a
name, a rune, `(:theorem term)`, `(:instance lmi (v t) ...)` (each `v` bound in
the lemma unless `:extra-bindings-ok`), `(:functional-instance lmi (f g) ...)`,
`(:termination-theorem fn)`, `(:guard-theorem fn)` [:doc lemma-instance].

### 3.2 `:cases`

When the rules need a condition the goal does not mention:
`:hints (("Goal" :cases ((< x 0))))` gives each rule's case its hypothesis.
Splits without rewriting; not inherited [:doc hints]
[example: examples/prover/cases-hint.lisp].

### 3.3 `:expand`

When the heuristics decline to open a call: `(equal (len (tk 1 x)) 1)` fails
with "No induction schemes are suggested" and proves with `:hints (("Goal"
:expand ((tk 1 x))))`. `(:free (vars) pat)`, `(:with name term)`, `:lambdas`
also exist [:doc hints] [example: examples/prover/expand-hint.lisp].

### 3.4 `:induct`

`:induct t` inducts now; `:induct term` uses `term`'s scheme; to reproduce the
prover's own choice give the suggesting term and every accommodated term,
`(list term0 ... termk)` [:doc hints]. Put a subgoal's `:induct` on the
subgoal's name, not on `*1.1` [:doc goal-spec]
[example: examples/prover/induct-hint.lisp]:

```lisp
(defthm len-of-tk-plus-1-by-hints
  (implies (natp n)
           (equal (len (tk (+ 1 n) x)) (+ 1 n)))
  :hints (("Goal" :induct (tk n x)
                  :expand ((tk 1 x))))
  :rule-classes nil)
```

Better, the general lemma `(defthm len-of-tk (equal (len (tk n x)) (nfix
n)))`, after which the special case needs no hint
[example: examples/prover/induct-hint.lisp].

Pitfall: a wrong `:induct` breaks a proof that succeeds unaided; try without
first: `(implies (and (natp i) (natp n) (< i n)) (equal (nth i (tk n x))
(nth i x)))` proved unaided and failed under `:induct` of a function
decrementing `i` and `n` together [measured: the two `thm` forms on that
statement, with and without the hint, after the `tk` defun, laptop REPL, ACL2
8.7 / SBCL 2.6.8].

### 3.5 `:in-theory`, and the subgoal pitfall

`:in-theory` is "evaluated relative to the current ACL2 logical world, not
relative to the theory of a previous goal" [:doc hints]. Pitfall: a subgoal hint
with its own `:in-theory` silently drops the `Goal` hint's disables; "the
`disable` of `f` on behalf of the hint at `Goal` will be lost at `Subgoal 3`"
[:doc hints]. In the example the subgoal hints below make a failing proof
*succeed*, because `f` is enabled again at both subgoals
[example: examples/prover/subgoal-theory.lisp]:

```lisp
(defthm f-of-natp
  (implies (natp x) (equal (f x) (+ 1 x)))
  :hints (("Goal" :in-theory (disable f (:e f))
                  :cases ((equal x 0)))
          ("Subgoal 2" :in-theory (enable gg))
          ("Subgoal 1" :in-theory (enable gg)))
  :rule-classes nil)
```

Rules: to hold everywhere, close it in the book (`(local (in-theory (disable
...)))` above the form), not in a `Goal` hint; a subgoal hint that means "Goal's
theory plus this" spells the whole `e/d` again
[fn: docs/proof-style.md:700 @3bbfc4dca]. fn's measured cost: a book from
609.53 s to 6.54 s once closed at the top [fn: docs/proof-style.md:673 @3bbfc4dca].

### 3.6 `:do-not`, `:do-not-induct`

`:do-not '(generalize)` stops an invented generalization; the list is
`preprocess simplify eliminate-destructors fertilize generalize
eliminate-irrelevance` [:doc hints]. `:do-not-induct t` fails at the first push
for induction: a fast "does simplification alone do this?" probe
[example: examples/prover/step-limits.lisp].

### 3.7 `:nonlinearp`, `:by`, `:restrict`, `:clause-processor`

- Products of unknowns need `:hints (("Goal" :nonlinearp t))` (default `nil`);
  `(set-non-linearp t)` is book-local [:doc hints], [:doc set-non-linearp]
  [example: examples/prover/nonlinearp.lisp].
- `:hints (("Goal" :by drop-of-drop))`: the goal is the instance or subsumed by
  it, no search. `:by nil` skips a goal and prints the `defthm`s still owed;
  such a proof is not a proof [:doc hints]
  [example: examples/prover/by-and-restrict.lisp].

- `:restrict` fixes a free variable's binding for one rule; ignored by the
  preprocessor [:doc hints] [example: examples/prover/by-and-restrict.lisp]:

  ```lisp
  (defthm subsetp-evens-evens
    (subsetp (evens (evens l)) l)
    :hints (("Goal" :restrict ((subsetp-trans ((y (evens l))))))))
  ```

- `:clause-processor`: the term in the hint must be *translated*;
  `'(<= 0 (mag y))` was refused with "did not evaluate to a list of clauses",
  `'(not (< (mag y) '0))` works [measured: the hint of
  examples/prover/clause-processor.lisp, untranslated]
  [example: examples/prover/clause-processor.lisp]:

  ```lisp
  (defthm twice-mag-non-negative
    (implies (rationalp y) (<= 0 (+ (mag y) (mag y))))
    :hints (("Goal" :clause-processor
                    (note-fact-clause-processor clause '(not (< (mag y) '0))))
            ("Subgoal 1" :in-theory (enable mag))))
  ```

  Trusted (unverified) clause processors need a ttag
  [:doc define-trusted-clause-processor].

### 3.8 Computed and default hints

Inject a hint only once a goal is stable; removed from children unless
`:computed-hint-replacement t` [:doc computed-hints]. `set-default-hints` is
book-local and comes after explicit hints [:doc set-default-hints]
[example: examples/prover/computed-hints.lisp]:

```lisp
(defthm mag-non-negative
  (implies (rationalp x) (<= 0 (mag x)))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable mag)))))

(set-default-hints '((and stable-under-simplificationp
                          '(:in-theory (enable mag)))))
```

Also: `:or`, `:hands-off`, `:backchain-limit-rw`, `:case-split-limitations`,
`:no-thanks`, `:instructions`, `:backtrack` [:doc hints].

## 4. Induction

### 4.1 What suggests a scheme

A call suggests its function's scheme "only if the controlling actuals are
distinct variables"; `(append (foo x) y)` does not [:doc induction]. The
message names the scheme and the accommodated terms; read it:

```
We will induct according to a scheme suggested by (DROP I X), while
accommodating (DROP J X), (DROP J (DROP I X)) and (DROP I (DROP J X)).
```

[measured: the `drop` commutation `thm`, examples/prover/induction-lemma-first.lisp].
Remedies are terms: rewrite the conjecture so the right call appears, `:induct
term`, or an `:induction` rule (6.9). Any admissible recursion is a scheme, so
a function written only to be named in `:induct` is the general tool
[:doc logic-knowledge-taken-for-granted-inductive-proof].

### 4.2 `No induction schemes are suggested`

```
No induction schemes are suggested by *1.  Consequently, the proof
attempt has failed.
```

[measured: the first `thm` of examples/prover/induct-hint.lisp]. Cause:
non-variable controlling arguments (`(tk (+ 1 n) x)`), or mutual recursion.
Fix with `:induct` (3.4), or a general lemma.

### 4.3 Mutual recursion: `tools/flag`

[books: tools/flag.lisp:93] [example: examples/prover/mutual-recursion-flag.lisp]:

```lisp
(include-book "tools/flag" :dir :system)

(mutual-recursion
 (defun tcopy (x)
   (if (atom x) x (cons (car x) (lcopy (cdr x)))))
 (defun lcopy (l)
   (if (atom l) l (cons (tcopy (car l)) (lcopy (cdr l))))))

(make-flag tcopy)

(defthm-flag-tcopy
  (defthm tcopy-is-identity
    (equal (tcopy x) x)
    :flag tcopy)
  (defthm lcopy-is-identity
    (equal (lcopy l) l)
    :flag lcopy))
```

The theorems must use the flag function's formals as variable names
[books: tools/flag.lisp:93].

## 5. Step and time limits

- `(with-prover-step-limit n form)` limits one form; `(set-prover-step-limit
  n)` is book/`encapsulate`-local and charges compound events as a whole
  [:doc with-prover-step-limit], [:doc set-prover-step-limit].
- `(with-prover-time-limit time form)`: runtime (CPU) by default; an inner
  limit cannot extend an outer one unless written `'(time)`; prints `ACL2
  Error [Time-limit] ... Out of time in ...` [:doc with-prover-time-limit]
  [measured: `(with-prover-time-limit 1/1000 (defthm ...))` at the laptop REPL].
- Pitfall: "An `ACL2 Error [Step-limit]` says the form did not finish inside
  `n`; it says nothing about whether the form closes, how it splits, or
  whether the change under test helped" [fn: docs/proof-style.md:650
  @3bbfc4dca]. "a `yes` is evidence while a `no` is not"; to compare, run
  without a limit under a wall-clock `timeout` and read `Time:` and the profile
  [fn: docs/proof-style.md:666 @3bbfc4dca].
- Books prefer step limits to time limits: "Avoid short proof timeout windows
  ... use step limits instead" [:doc best-practices].
- A deliberate failure in a book: `must-fail` around a step-limited form, so it
  certifies fast [example: examples/prover/induction-lemma-first.lisp]:

  ```lisp
  (local
   (must-fail
    (with-prover-step-limit 200000
      (thm (implies (and (natp i) (natp j))
                    (equal (drop i (drop j x))
                           (drop j (drop i x))))))))
  ```

## 6. Rules: how they are made, why they do not fire

### 6.1 Rule classes

Default is `:rewrite`; `:rule-classes nil` makes no rule; `:corollary` stores a
different form than the one stated. "new ACL2 users rely almost exclusively on
(conditional) rewrite rules", plus `:type-prescription` and
`:forward-chaining` for type-like facts [:doc rule-classes]. `defthmd` proves
and disables [:doc defthmd]. Inspect a stored rule with `:pr name` (`Hyps`,
`Equiv`, `Lhs`, `Rhs`, `Loop-stopper`) [:doc pr]. A predicate conclusion
becomes `(iff p t)`: it fires only in propositional positions [:doc rewrite].

Read these warnings at storage time; each says the rule will rarely fire:

```
ACL2 Warning [Non-rec] in ( DEFTHM F1-IS-F2 ...):  A :REWRITE rule
generated from F1-IS-F2 will be triggered only by terms containing
the function symbol F1, which has a non-recursive definition.  Unless
this definition is disabled, this rule is unlikely ever to be used.
```

[measured: `(defthm f1-is-f2 ...)` of examples/rewriting/loop-pair.lisp before
`f1` is disabled]. `[Subsume]` says an older rule matches a more general
target; `[Free]` says a hypothesis has a free variable (6.4).

### 6.2 Non-recursive functions in hypotheses

Pitfall: hypothesis `(my-statep s)` with `my-statep` enabled and non-recursive:
the goal's own copy has already opened, so the hypothesis does not match. "beware
of non-recursive functions occurring in the hypotheses of `:type-prescription`
rules"; disable the predicate or write its body in the hypothesis
[:doc type-prescription], [:doc free-variables]. (This guide's reconstruction
of the manual's example did prove; the rule is the manual's claim
[measured: `my-statep` with a constrained `sget` and a `:type-prescription`
rule, laptop REPL, ACL2 8.7 / SBCL 2.6.8].)

### 6.3 `force`, `case-split`, `syntaxp`, `bind-free`

- `force`: assume the hypothesis if not provable, prove it in a later forcing
  round. Only for hypotheses "expected always to be true" [:doc force].
  "q.e.d. (given one forced hypothesis)" then a failed "Forcing Round 1" means
  the context did not establish it, not that the rule is wrong
  [example: examples/rewriting/force.lisp].

- `case-split`: the false case is a subgoal now, not a forcing round
  [:doc case-split]. Neither acts while an `if` is in the goal [:doc force].
- `syntaxp`: a meta-level test on the *quoted term* each variable matched;
  stops a rule that rewrites its own output
  [:doc syntaxp] [example: examples/rewriting/syntaxp.lisp]:

  ```lisp
  (defthm lxd-normalize
    (implies (syntaxp (not (and (consp x) (eq (car x) 'nrm))))
             (equal (lxd x) (lxd (nrm x))))
    :hints (("Goal" :use ((:instance lxd-of-nrm)))))
  ```

- `bind-free`: returns alists binding free variables; name the variables in
  the second argument [:doc bind-free] [example: examples/rewriting/bind-free.lisp]:

  ```lisp
  (defun lo-candidates (x)
    (declare (xargs :guard t))
    (list (list (cons 'y (list 'cons x ''3)))
          (list (cons 'y (list 'cons x ''4)))))

  (defthm lo-implies-hi-with-candidates
    (implies (and (bind-free (lo-candidates x) (y))
                  (lo x y))
             (hi x)))
  ```

### 6.4 Free variables

A variable in hypothesis `hi` not in the left side or an earlier hypothesis is
free; it is bound by (1) a binding hypothesis `(equal var term)`, (2) a matching
known assumption, (3) a hypothesis-free ground rewrite rule [:doc free-variables].
`:match-free :once` keeps the first binding; `:all` backtracks; absent a
setting the default is `:all`, with a warning [:doc free-variables],
[:doc set-match-free-error]. Put "more substantial" hypotheses first; a cheap
`(rationalp y)` first binds `y` to the first rational in sight
[:doc free-variables]. In the example, transitivity with `:rule-classes
((:rewrite :match-free :once))` fails and with `:match-free :all` proves
[example: examples/rewriting/free-variables.lisp].

When the binding fact is a rule, not a context fact: `bind-free` (6.3),
`:restrict` (3.7), or a `:forward-chaining` rule that puts the fact in the
context [:doc forward-chaining] [example: examples/rewriting/forward-chaining.lisp].

### 6.5 Loops

How it prints:

```
HARD ACL2 ERROR [Call depth] in REWRITE:  The call depth limit of 1000
has been exceeded in the ACL2 rewriter.  To see why the limit was exceeded,
first execute
  :brr t
and then try the proof again, and then execute the form (cw-gstack)
or, for less verbose output, instead try (cw-gstack :frames 30).
```

[measured: the looping `thm` of examples/rewriting/loop-pair.lisp]. `in
PREPROCESS` means the loop is in abbreviation rules; retry with `:do-not
'(preprocess)` [measured: the looping `thm` of examples/rewriting/syntaxp.lisp].
A silent prover is a loop that does not deepen the stack, or a case explosion
[:doc introduction-to-key-checkpoints]. `(cw-gstack :frames '(5 12))` after
`:brr t` shows the alternating rules [example: examples/rewriting/loop-pair.lisp].

Fix: choose one normal form, disable the other direction, record the choice
[example: examples/rewriting/loop-pair.lisp], [:doc best-practices]:

```lisp
(in-theory (disable f2-is-f1))

(theory-invariant (incompatible (:rewrite f1-is-f2) (:rewrite f2-is-f1))
                  :key f1-f2-direction)
```

A rule can be "never-useful by the profile yet load-bearing": its being
enabled keeps two other rules from looping [fn: docs/proof-style.md:549
@3bbfc4dca]; write that as a `theory-invariant`, not prose.

### 6.6 Loop-stoppers

A permutative rule (rhs an instance of lhs by a variable renaming) gets a
loop-stopper and sorts its arguments [:doc loop-stopper]. `:loop-stopper nil`
removes it and the rule loops on `(op b a)`
[example: examples/rewriting/loop-stopper.lisp]. A non-permutative self-feeding
rule gets none: use `syntaxp` (6.3).

### 6.7 `:type-prescription`, `:forward-chaining`, `:linear`

- `:type-prescription`: hypotheses relieved "by type reasoning alone, not
  rewriting!" [:doc type-prescription].
- `:forward-chaining`: hypotheses by type reasoning, ground evaluation and
  known assumptions; conclusion goes into the context "with no simplification
  or rewriting", invisible in the goal; trigger defaults to the first
  hypothesis, `:trigger-terms` for others [:doc forward-chaining]. Use it for
  widely needed facts you do not want as rewrite rules (fn's record shape
  facts) [fn: docs/proof-style.md:153 @3bbfc4dca].
- `:linear`: an inequality stored under its maximal terms, relieved by
  rewriting; a bound linear arithmetic cannot finish with the functions closed
  closes once the same fact is `:rule-classes :linear`
  [:doc linear] [example: examples/rewriting/linear.lisp]. Pitfall: a `:linear` rule with `:trigger-terms` and a `:rewrite` class on one
  conclusion crashed SBCL; split it [fn: docs/proof-style.md:911 @3bbfc4dca].
- A type goal like `(INTEGERP (+ AMT (BAL ...)))` is settled by type reasoning,
  which never calls the rewriter: a rewrite rule concluding `(integerp ...)`
  does not reach it; use `:type-prescription` + `:linear`
  [example: examples/stobjs/nested-stobj.lisp], [example: examples/stobjs/local-stobj.lisp].

### 6.8 `:definition`, `:congruence`, `:compound-recognizer`, tau

- `:definition`: an alternative body, controlled like a definition
  [:doc definition] [example: examples/rewriting/definition-rule.lisp].
- Equivalences: `defequiv`, then `defcong` before rules under the equivalence
  can be used inside a function [:doc congruence]
  [example: examples/rewriting/congruence.lisp]:

  ```lisp
  (defequiv lequiv)
  (defcong lequiv equal (cnt x) 1
    :hints (("Goal" :in-theory (enable lequiv)
                    :use ((:instance cnt-of-lfix-lemma (x x))
                          (:instance cnt-of-lfix-lemma (x x-equiv))))))
  ```

- `:compound-recognizer` tells type reasoning what a recognizer implies
  [:doc compound-recognizer]. With tau on (the default) the same goal may
  prove without it [example: examples/rewriting/compound-recognizer.lisp].
- Tau: `(in-theory (disable (tau-system)))` turns it off [:doc tau-system].
  Keep it on by default; fn measured tau off cost 1,400 s more than it saved
  over 1,445 books; turn it off only where measured
  [fn: docs/proof-style.md:633 @3bbfc4dca].

### 6.9 `:induction` rules

Disabling `(:induction fn)` stops `fn` suggesting its scheme; a user rule links
a pattern to a scheme, theorem `t` [:doc induction]
[example: examples/rewriting/induction-rule.lisp]:

```lisp
(defthm drop-suggests-tk-induction
  t
  :rule-classes ((:induction :pattern (drop n x)
                             :scheme (tk n x))))
```

### 6.10 Normal forms

Every rule picks a normal form; two rules that disagree loop. Name a rule by
its left side with `of`: `append-of-cons`; `-when-hyp`, `-under-equiv`
[books: doc/practices.lisp:511]. Leave `mv-nth` disabled and write lemmas with
it [:doc conventional-normal-forms]. fn: after a record's lemmas, its
definitions are withdrawn; "Nothing below that point opens a record"
[fn: docs/proof-style.md:81 @3bbfc4dca]. Opening a vocabulary book-wide breaks
the normal form: domain lemmas "stopped matching the induction goals"
[fn: docs/proof-style.md:747 @3bbfc4dca].

## 7. Tools inside a proof

- `accumulated-persistence`, first on any slow form [:doc accumulated-persistence],
  [fn: docs/proof-style.md:561 @3bbfc4dca]:

  ```lisp
  (accumulated-persistence t)
  (thm ...)
  (show-accumulated-persistence :frames)
  (accumulated-persistence nil)
  ```

  Large useless `:frames` with small useful counts: candidates to disable; the
  top rune may be billed for another's work; after an abort use `:frames-a`
  [:doc accumulated-persistence]. "A lane that reaches for `minimal-theory`
  instead has skipped this step" [fn: docs/proof-style.md:588 @3bbfc4dca].
- Break-rewrite: `:brr t`, `:monitor (:rewrite name) t`, then in the break
  `:target`, `:unify-subst`, `:path`, `:eval`, `:failure-reason`, `:ok`, `:go`,
  `:a!`; `:brr nil` when done [:doc break-rewrite], [:doc monitor]. A monitored
  rule that never breaks: brr off, rune disabled, abbreviation tried only in
  preprocess (`:do-not '(preprocess)`), `:hands-off`, inside `HIDE`, no target
  [:doc monitor].
- `(cw-gstack)` after an interrupt or loop, with `brr` on [:doc cw-gstack];
  `(pstack)` after an abort [:doc pstack]; `dmr` needs Emacs on the same
  machine [:doc dmr].
- History: `:pe name`, `:pl term` (rules possibly applicable), `:pr name`,
  `:pbt`, `:ubt` (undoes command blocks) [:doc pe], [:doc pl], [:doc pr],
  [:doc pbt], [:doc ubt].

## 8. Theories and the export boundary

### 8.1 Designators

`fn` = `(:definition fn)` + `(:induction fn)`, not the executable counterpart;
`(fn)` = `(:executable-counterpart fn)`; abbreviations `(:d fn) (:e fn) (:i fn)
(:r name) (:t fn)`; a theorem name = all its rules [:doc theories]. `defund`
leaves exactly the definition and induction disabled
[example: examples/rewriting/theories.lisp]:

```lisp
(defund fact (n)
  (if (zp n) 1 (* n (fact (1- n)))))

(assert-event (equal (disabledp 'fact)
                     '((:definition fact) (:induction fact))))
```

### 8.2 Expressions and named theories

`(enable ...)`, `(disable ...)`, `(e/d (en) (dis))`; surround `in-theory` with
`local` [:doc enable], [:doc disable], [:doc e/d], [:doc in-theory]. Name a
vocabulary so an includer re-enables it in one hint; prove primitive-only
lemmas in `ground-zero` [fn: docs/proof-style.md:215 @3bbfc4dca],
[fn: docs/proof-style.md:432 @3bbfc4dca] [example: examples/rewriting/theories.lisp]:

```lisp
(deftheory fact-vocabulary
  '((:d fact) (:i fact)))

(defthm fact-positive
  (implies (natp n) (< 0 (fact n)))
  :hints (("Goal" :in-theory (enable fact-vocabulary))))

(defthm len-of-append-in-ground-zero
  (equal (len (append x y))
         (+ (len x) (len y)))
  :hints (("Goal" :in-theory (theory 'ground-zero))))
```

`minimal-theory` is for proofs from `:use`d lemmas [:doc minimal-theory];
reaching for it is a smell: "a book that exported too much; say which rules
you mean with `e/d`" [fn: docs/proof-style.md:534 @3bbfc4dca]. A `deftheory`
over `(current-theory :here)` can differ at include time; use
`deftheory-static` [:doc deftheory-static].

### 8.3 Executable counterparts

Disabling `(:e f)` stops ground evaluation; the definition alone will not open
`(fact 5)` five times [example: examples/rewriting/theories.lisp]
[:doc executable-counterpart]. A ground call reaching a constrained function
becomes a `HIDE`; disable the executable counterpart of functions that call
constrained ones [:doc functional-instantiation-example].

### 8.4 `local`, `encapsulate`, functional instances, `defattach`

- `(local ev)` runs during admission and is skipped on include; "you can't make
  an event local if its presence is required to make sense of a non-local one"
  [:doc local].
- `encapsulate` makes two passes; local witnesses prove the constraints
  consistent; errors are a local function used non-locally, or a signature's
  witness not local; no `defaxiom` inside, no non-local `include-book` inside one
  with signatures [:doc encapsulate], [:doc local-incompatibility].
- Functional instance: obligations are the replaced functions' constraints;
  defined functions over constrained ones are replaced too [:doc lemma-instance]
  [example: examples/books/encapsulate-fi.lisp]:

  ```lisp
  (defthm integer-listp-of-append-fi
    (implies (true-listp x)
             (equal (integer-listp (append x y))
                    (and (integer-listp x) (integer-listp y))))
    :hints (("Goal" :use ((:functional-instance all-ok-of-append
                                                (ok integerp)
                                                (all-ok integer-listp))))))
  ```

- `(defattach better greater-rationalp)` makes constrained `better` evaluate
  through `greater-rationalp`: `(best '(3 1 2))` then evaluates to `3`, and a
  `thm` of the same equality still fails, since attachments are not used for
  ground terms in proofs [:doc defattach]
  [example: examples/books/defattach-exec.lisp].

### 8.5 What a book exports

- A `local` include is the book's private tool; the includer gets non-local
  events only [example: examples/books/lib.lisp], [example: examples/books/user.lisp].
- A non-local include enables everything the included book leaves enabled, in
  every includer above: fn's `bp-ingress` went from six minutes to an 1800 s
  timeout, "1.92M backchain frames of which none contributed"
  [fn: docs/proofs.md:257 @3bbfc4dca].
- End every book with an explicit theory event; the book's own theorems come
  before it, "so a book's own proofs never depend on what an includer happens
  to have enabled" [fn: docs/proof-style.md:186 @3bbfc4dca],
  [fn: docs/proof-style.md:237 @3bbfc4dca] [example: examples/books/lib.lisp]:

  ```lisp
  (deftheory lib-internals
    '((:d sum-list) (:i sum-list)))

  (in-theory (disable lib-internals))
  ```

- Never leaves a book enabled: "record accessors, constructors and shapes;
  recognizers of records and states; initial states; transitions; `len`-,
  `consp`- or `true-listp`-backchaining rules; `-is-`/`-of-` equalities other
  than record lemmas; proof-vocabulary lemmas ...; corollaries"
  [fn: docs/proof-style.md:529 @3bbfc4dca].
- An includer needing withdrawn vocabulary enables it in the one hint that
  needs it, "never with a book-level `(in-theory (enable ...))`"
  [fn: docs/proof-style.md:747 @3bbfc4dca].
- Library etiquette: no non-local arithmetic includes; no non-local
  `in-theory` on built-ins; includes and `in-theory` at the top and local;
  most functions disabled [:doc theory-management], [:doc best-practices].

## 9. Books and certification

### 9.1 What certification does and requires

`certify-book` checks every form, re-includes the book to catch local
incompatibilities, and writes a certificate with the portcullis and a
book-hash per included book; every included book must already be certified;
guard checking is `t` and the default mode `:logic` [:doc certify-book].
`include-book` of an uncertified book succeeds with a warning unless
`:uncertified-okp nil` [:doc include-book]. Use `:dir :system` for community
books, relative paths only inside one library, never absolute
[:doc best-practices].

### 9.2 Portcullis, packages, products

- `defpkg` "should not occur in books"; it goes in the portcullis, i.e. a
  `foo.acl2` or `cert.acl2` for `cert.pl` [:doc defpkg], [books: build/doc.lisp:558].
  Packages for many books: `package.lsp` + `portcullis.acl2` + empty
  `portcullis.lisp` + `cert.acl2` including it [:doc working-with-packages].
- Products: `.cert`, `.cert.out` (the log), `.fasl` on SBCL, `.port`,
  `Makefile-tmp` [books: build/doc.lisp:297], [measured: `ls examples/books/`].
  The `.fasl` loads only if not older than the `.cert` [:doc include-book],
  [fn: docs/proofs.md:351 @3bbfc4dca].
- `cert.pl` rebuilds uncertified dependencies; `-j N` is memory-bound;
  an `include-book` with the name on the next line is invisible to its
  scanner [books: build/doc.lisp:297]. Here: `examples/certify.sh`.
- Book hashes, closures and caches: `ai/06-process-and-repl.md` section 8.

### 9.3 Provisional certification

Create (`.pcert0`, proofs skipped), Convert (`.pcert1`, proofs), Complete
(rename to `.cert`); `cert.pl --pcert-all -j 4` [:doc provisional-certification].
Complete "only checks write dates"; for trust certify from scratch
[:doc provisional-certification]. Use it for triage only: one round names
every independent red; "**A triage run is evidence of nothing but its list of
reds**" [fn: docs/proofs.md:554 @3bbfc4dca], [fn: docs/proofs.md:588 @3bbfc4dca].

### 9.4 `make-event`

Expanded at certification, the expansion recorded and reused on include
unless `:check-expansion t` [:doc make-event]. Use it to refuse certification
unless a check holds, and to record a constant computed from the world
[example: examples/books/make-event-check.lisp].

### 9.5 `assert-event`

An event; errors when the form is `nil`; skipped when proofs are skipped (so on
include) unless `:on-skip-proofs t` [:doc assert-event]. Use it for
counterexamples and world checks [example: examples/books/user.lisp]:

```lisp
(assert-event
 (not (getpropc 'sum-list-of-append-local 'theorem nil (w state))))
```

### 9.6 `must-fail`

Passes when the form returns a soft error; `:expected :hard` / `:any` widen it
[books: std/testing/must-fail.lisp:17]. Make it `local` when it wraps a `thm`,
or the book may not include [books: std/testing/must-fail.lisp:17]. Pitfall:
"Never a general negated `must-fail`: it proves that the prover could not find
a proof, which is not a counterexample" [fn: docs/proof-style.md:381
@3bbfc4dca]. A `must-fail` beside no concrete value is labelled `; teeth:
prover-refusal REASON` [fn: docs/proof-style.md:389 @3bbfc4dca]
(`ai/06-process-and-repl.md` section 2).

## 10. `skip-proofs`, `defaxiom`, trust tags

- `skip-proofs` "can even allow inconsistent events to be admitted"; a script
  with it is "work-in-progress, not ... a completed proof"; certification
  refuses it unless `:skip-proofs-okp t` [:doc skip-proofs], [:doc certify-book].
- `defaxiom`: never. "Note that adding new axioms may frequently render the
  logic inconsistent!" [:doc defaxiom]. State an assumption as an `encapsulate`
  with a local witness (`ai/04-modelling.md` section 9).
- Trust tags (`sys-call`, `progn!`, trusted clause processors) are a contract
  the certificate records; audit `TTAG NOTE`s [:doc defttag].
- fn: "Do not turn `skip-proofs`, trust tags, or axioms into a certification
  shortcut"; disclose trusted facilities [fn: docs/proofs.md:85 @3bbfc4dca].

## 11. Example index

`examples/prover/*.lisp` (sections 2 to 5: one hint or failure mode each, most
with a `local` `must-fail` of the first attempt), `examples/rewriting/*.lisp`
(section 6: one rule class or rewriting technique each),
`examples/books/*.lisp` (sections 8 and 9: `local`, export theory, functional
instance, `defattach`, `make-event`). Each header says what it shows.
