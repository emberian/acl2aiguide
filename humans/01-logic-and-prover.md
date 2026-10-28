# 1. The logic and the prover

This chapter is about the theorem prover: what it is proving things about,
what it does with a conjecture, how a failed proof reads, and how to steer it
with hints. Chapter 2 is about the rules the prover rewrites with, the
theories that switch them on and off, and the books that carry them.

Every technique here has a small certified book under `examples/prover/`.
Each book states, in its header, what it shows; each was certified with
`examples/certify.sh` on the laptop ACL2 (8.7 on SBCL 2.6.8) before it was
cited. Most of them contain a `must-fail` of the first attempt, so the book
records the failure as well as the repair. Prover output quoted below was
produced at the laptop REPL (`~/tools/acl2-fn/acl2-literal-4g-tls64k`) from the
forms of the cited example; the `[measured: ...]` tag names the form.

## 1.1 Pitfalls first

The failures a new user meets, in roughly the order they are met, and where
this chapter takes each apart:

1. **The conjecture is false.** A checkpoint after induction that is not a
   theorem means the original conjecture is not a theorem; evaluate it on
   small constants before doing anything else (section 1.6.4,
   `examples/prover/false-conjecture.lisp`).
2. **The statement is too specific for induction.** A theorem about an
   accumulator function stated only for the initial accumulator fails; the
   general statement proves (section 1.6.5,
   `examples/prover/induction-accumulator.lisp`).
3. **A lemma is missing, and ACL2 inducts anyway.** The prover finds an
   induction and fails in sub-inductions, when one rewrite rule would have
   made induction unnecessary (section 1.6.5,
   `examples/prover/induction-lemma-first.lisp`).
4. **No induction is suggested.** Every recursive call in the goal has a
   non-variable controlling argument, or the functions are mutually
   recursive (section 1.9, `examples/prover/induct-hint.lisp`,
   `examples/prover/mutual-recursion-flag.lisp`).
5. **A `:use` hint did nothing.** The lemma was also an enabled rewrite rule
   and rewrote its own instance to `T` (section 1.8.2,
   `examples/prover/use-instance.lisp`).
6. **A `Goal` `:in-theory` was silently undone** by a subgoal hint with its
   own `:in-theory` (section 1.8.6, `examples/prover/subgoal-theory.lisp`).
7. **The prover went silent.** A rewrite loop or a case explosion; see the
   tools of section 1.7 and the loop chapter of chapter 2.
8. **A probe was stopped by a step limit, and the stop was read as a
   result.** It is not one (section 1.10, `examples/prover/step-limits.lisp`).
9. **The time went somewhere other than the rewriter.** Read the `Time:` line
   before reading the subgoals (section 1.6.6).

## 1.2 What ACL2 is

### 1.2.1 A first-order logic of total functions over a fixed universe

ACL2's logic is based on Common Lisp: "ACL2 is a large subset of the
first-order **applicative** part of Common Lisp", without higher-order
features such as functional objects and `apply`, and without primitives with
side effects such as `setq` and `setf` [:doc |Common Lisp|]. The later
`apply$`, which provides "Limited Second-Order Functionality in a First-Order
Setting", is itself "the ACL2 function that takes two arguments, one
representing a function and the other listing actuals" [:doc apply$].

The universe of objects is fixed. "ACL2 provides five data types: numbers,
characters, strings, symbols, and ordered pairs" [:doc r-and-i-data-types].
The numbers are "the precisely represented, unbounded numbers (integers,
rationals, and the complex numbers with rational components, called the
``complex rationals'' here)"; the characters are those "with ASCII codes
between 0 and 255"; symbols include packages [:doc |Common Lisp|]. "Objects of
each type are distinct. That is, no number is a character or a string or a
symbol or a pair" [:doc gentle-introduction-to-ACL2-programming].

The logic is untyped: "it is legal to apply a function symbol of n arguments
to any n terms, regardless of the types of the argument terms", so `(+ t 3)`
is a term, and "the axioms actually define a value for such terms. The value
of `(+ t 3)` is 3; under the ACL2 axioms, non-numeric arguments to `+` are
treated as though they were 0" [:doc |About Types|]. Every function is total:
"ACL2 is a syntactically untyped language and all functions are defined on
all objects in the ACL2 universe" [:doc frequently-asked-questions-by-newcomers].
The same holds for the primitives: in a computed hint, which is evaluated
with guard checking off, "the form `(car 23)` ... returns `nil` as per the
axioms" [:doc computed-hints].

Totality is the first source of surprises. A conjecture you believe about
the inputs you have in mind is a conjecture about **all** objects, and the
"unusual cases (like `(+ t 3)`) can arise" [:doc |About Types|]. Section 1.6.4
shows a conjecture about list prefixes that is false only because the
function pads with `NIL` when the list runs out
[example: examples/prover/false-conjecture.lisp].

What plays the role of a type signature is the guard: "the *guard* of a
function is akin to the type signature of a function in typed languages.
However, ACL2 guards may be arbitrary terms, not just type conditions, they
only concern the inputs to the function (not its result), and do not affect
the axiom defining the function" [:doc frequently-asked-questions-by-newcomers].
Guards are the subject of the modelling chapter; here it is enough that "the
guard of `fn` has no bearing on this logical axiom" [:doc defun].

### 1.2.2 Every function executes: `:logic` and `:program` mode

An ACL2 function is both a definition in the logic and a Common Lisp
program. "Two ``defun-modes'' are supported, `:program` and `:logic`. Roughly
speaking, `:program` mode allows you to prototype a function for execution
without any proof burdens, while `:logic` mode allows you to add a new
definitional axiom to the logic. The system comes up in `:logic` mode"
[:doc defun-mode].

A `:program` function has no axiom: "the ACL2 theorem prover knows no axioms
about `fact`. In particular, if the term `(fact 3)` arises in a proof, the
theorem prover is unable to deduce that it is `6`", and "we do not allow
`fact` to be used in logical contexts such as conjectures submitted for
proof" [:doc defun-mode]. A `:logic` function may call only `:logic`
functions: "every function called by the newly defined one must be in
`:logic` mode" [:doc defun-mode].

Converting a function from `:program` to `:logic` mode is
`(verify-termination fact)`, "which is equivalent to submitting the `defun`
of `fact`, again, but in `:logic` mode", at the cost of the termination proof
[:doc defun-mode]. In a book the mode is changed with the embedded event form
`(program)` or `(logic)`, not with the keyword commands `:program` or
`:logic`, which "is not a legal form for books"; the change is local to the
book or `encapsulate` [:doc program], [:doc logic].

`:program` mode is not free of risk. "Execution of functions whose
defun-mode is `:program` may render ACL2 unsound!" because a `:program`
function's guard has not been checked to protect its subroutines; the manual
calls this concern "extremely paranoid" but documents it [:doc defun-mode],
[:doc defun-mode-caveat].

## 1.3 Definitions and the admission obligations

### 1.3.1 What `defun` adds

Provided a definition is admissible, `defun` adds its equation as an axiom,
"implemented in the ACL2 system by a `:definition` rule"; replacing a call by
its instantiated body is called "opening up" the call, and which calls are
opened "are chosen primarily by heuristics" [:doc defun]. A `defun` creates up
to four runes: `(:definition fn)`, `(:executable-counterpart fn)`, possibly
`(:type-prescription fn)`, and, for a recursive function, `(:induction fn)`
[:doc rune].

### 1.3.2 The admission conditions

The manual states the syntactic conditions as follows: "First, `fn` must be a
previously unaxiomatized function symbol ... Second, the formal parameters
must be distinct variable names. Third, the guard, measure, and body should
all be terms and should mention no free variables except the formal
parameters" [:doc defun]. Then termination: "there must exist a binary
relation, `rel`, and some unary predicate `mp` such that `rel` is well-founded
on objects satisfying `mp`, the measure term `m` must always produce something
satisfying `mp`, and the measure term must decrease according to `rel` in each
recursive call, under the hypothesis that all the tests ruling the call are
satisfied" [:doc defun].

For the default relation the obligations are two theorems. For the generic
definition

```lisp
(defun fn (x y)
  (declare (xargs :guard (g x y)
                  :measure (m x y)))
  (if (test x y)
      (stop x y)
    (step (fn (d x) y))))
```

ACL2 must prove `(o-p (m x y))` and
`(implies (not (test x y)) (o< (m (d x) y) (m x y)))` [:doc defun].

### 1.3.3 Measures and ordinals

"The default well-founded relation is `o<`, an ``ordinal less-than'' relation
... that reduces to ordinary `<` on the natural numbers. The default measure
term is `(acl2-count var)`, where `var` is a formal parameter that is chosen
heuristically: roughly speaking, it is the first formal that is tested along
every branch and changed in each recursive call" [:doc defun]. `acl2-count`
gives characters and symbols count 0, a string its length, a cons one more
than the sum of its parts, an integer its absolute value [:doc acl2-count].
So recursion by `cdr` under a `consp` test, and recursion by `1-` on a
positive integer, are "trivially admitted" [:doc defun].

The ordinals ACL2 knows are those below epsilon-0, recognized by `o-p`. "The
sequence of `o-p`s starts with the natural numbers ... it means that if a
term, such as a measure expression ... must produce an `o-p`, it suffices for
it to produce a natural number" [:doc o-p]. An infinite ordinal is a list of
exponent-coefficient pairs ending in a natural; `'((1 . 1) . 0)` is omega
[:doc o-p]. For a measure that is a pair of numbers compared
lexicographically, the community book `ordinals/lexicographic-ordering`
provides `l<`; the manual's `mutual-recursion` topic shows a clique admitted
under `(set-well-founded-relation l<)` with measures `(list (acl2-count x) 1)`
and `(list (acl2-count y) 0)` [:doc mutual-recursion], [:doc ordinals].

The measure is given with `(declare (xargs :measure ...))`; `:measure` is not
allowed on a non-recursive definition outside a `mutual-recursion`, and is
ignored in `:program` mode [:doc xargs]. A different well-founded relation is
named with `:well-founded-relation`, which must be "known to be a well-founded
relation in the sense that a rule of class `:well-founded-relation` has been
proved about it" [:doc xargs].

### 1.3.4 Rulers: the tests that count

The termination obligation uses the tests that *rule* each recursive call,
not all the tests that *govern* it. "The set of rulers of the occurrence only
includes, at least by default, those tests and their negations from the
top-level `IF` structure of the term" [:doc rulers]. This definition fails
for that reason:

```lisp
(defun f (x)
  (cons 3
        (if (consp x)
            (f (cdr x))
          nil)))
```

`(consp x)` governs the call but sits under `cons`, so it does not rule it.
Two repairs: lift the test to the top, or "tell ACL2 to extend its termination
(and induction) analysis through calls of `cons`" with
`(declare (xargs :ruler-extenders (cons)))`, or `:ruler-extenders :all`
[:doc rulers]. `let` and `let*` are `lambda` applications and block the
analysis the same way; `:ruler-extenders (:lambdas)` lets it through
[:doc rulers]. Two warnings from the same topic: name functions, not macros,
as ruler-extenders (`binary-+`, not `+`), and "by taking advantage of the
ruler-extenders, you may change the induction scheme computed for the
function" [:doc rulers]. The topic `induction-coarse-v-fine-grained` explains
how a well-chosen setting gives inductions with more cases and fewer, more
relevant, induction hypotheses [:doc induction-coarse-v-fine-grained].

When ACL2 accepts a definition it prints the obligation it proved. For a
two-argument measure the manual shows

```
For the admission of G we will use the relation O< (which is known
to be well-founded on the domain recognized by O-P) and the measure
(+ (ACL2-COUNT X) (ACL2-COUNT Y)).  The non-trivial part of the measure
conjecture is
```

followed by the `o-p` and `o<` goals [:doc rulers]. A failed admission prints
those goals as checkpoints, and they are read like any other (section 1.6).

### 1.3.5 Mutual recursion

"When mutually recursive functions are introduced it is necessary to do the
termination analysis on the entire clique of definitions ... the callee's
actuals are measured as specified by the callee's `defun` while the caller's
formals are measured as specified by the caller's `defun`" [:doc
mutual-recursion]. Each member is a plain `defun` (or `defund`, `defun-nx`,
`defund-nx`), not a macro that expands to one [:doc mutual-recursion]. The
consequence for proofs is that "ACL2 does not know how to do inductions for
mutually recursive functions and must be told"
[:doc frequently-asked-questions-by-newcomers]; section 1.9.3 shows the tool
that tells it.

## 1.4 The induction principle

### 1.4.1 Induction is dual to recursion

Classical induction on the naturals is the scheme

```lisp
(implies (zp n) (p n))                                  ; base case
(implies (and (not (zp n)) (p (- n 1))) (p n))          ; induction step
```

and "the theorems proved when `nat-recursion` is introduced *justify* the
classical induction scheme" [:doc logic-knowledge-taken-for-granted-inductive-proof].
The general statement: "Every recursively defined ACL2 function suggests a
legal induction and vice versa", and "every legal ACL2 induction corresponds
to an admissible recursive function and vice versa" [:doc
logic-knowledge-taken-for-granted-inductive-proof].

What a function contributes to its scheme is its shape, not its value: "All
that matters is (i) how the `if` structure breaks down the cases ... (ii)
which branches lead to recursion, and (iii) what arguments are passed to the
recursive calls" [:doc logic-knowledge-taken-for-granted-inductive-proof].
Each induction hypothesis "is always an instance of the conjecture being
proved" [:doc logic-knowledge-taken-for-granted-inductive-proof].

### 1.4.2 Which terms suggest an induction

"The functions in a conjecture ``suggest'' the inductions considered by the
system" through their `:induction` runes, which the definitional principle
creates for each recursive function [:doc induction]. A call suggests its
function's scheme "only if the controlling actuals are distinct variables";
"`(append (foo x) y)` does not suggest an induction unwinding `append`"
[:doc induction]. The candidates are then combined: "ACL2 ... massages them
in various ways, combining some to simultaneously unwind certain cliques of
functions and vetoing others because they ``flaw'' others" [:doc induction];
the detailed account is the paper *ACL2 Induction Heuristics* linked from
[:doc induction-heuristics].

The prover reports this step in words. For the conjecture
`(equal (drop i (drop j x)) (drop j (drop i x)))` it says

```
Perhaps we can prove *1 by induction.  Four induction schemes are suggested
by this conjecture.  Subsumption reduces that number to two.  These
merge into one derived induction scheme.

We will induct according to a scheme suggested by (DROP I X), while
accommodating (DROP J X), (DROP J (DROP I X)) and (DROP I (DROP J X)).
```

[measured: `(thm (equal (drop i (drop j x)) (drop j (drop i x))))` after the
`defun` of `drop` in examples/prover/induction-lemma-first.lisp, laptop REPL,
ACL2 8.7 / SBCL 2.6.8]. "While accommodating" names the other terms that
took part; "the simplifier preferentially expands those terms during the
subsequent proof attempt" [:doc hints] (under `:induct`). The same message
also says, when it happens, "Note, however, that the unmeasured variables J
and X are being instantiated": the scheme replaces more than the measured
variable in the hypothesis [measured: same run].

Because a scheme is chosen from terms, the remedies for a wrong choice are
terms as well: write the conjecture so that the right call is present, give
an `:induct` hint whose term suggests the right scheme (section 1.9.1), or add
an `:induction` rule that links a pattern to a scheme (chapter 2).

## 1.5 The waterfall

### 1.5.1 The processes, in order

"Each goal considered by the ACL2 prover passes through a series of proof
processes, called the ``waterfall processes'', as stored in the constant
`*preprocess-clause-ledge*`. The top process applies top-level hints,
including `:use` hints; the next is a lightweight ``preprocess'' simplifier
for ``simple'' rules ...; that is followed by the main ACL2 simplifier and
then the ``settled-down'' process ...; and finally ACL2 attempts (in this
order) destructor elimination, fertilization (heuristic use of equalities),
generalization, and elimination of irrelevance" [:doc hints-and-the-waterfall].
Each process may hit, producing subgoals that each start again at the top, or
miss, passing the goal on; "If all processes miss, then a ``push'' process
defers the goal until it is later considered for proof by induction"
[:doc hints-and-the-waterfall].

The six techniques, in the tutorial's words [:doc architecture-of-the-prover]:

- *simplification*: "decision procedures and rewriting with previously proved
  rules ... Simplification is the only proof technique that can reduce a
  formula to 0 subgoals (i.e., prove it) rather than just transform it to
  other formulas";
- *destructor elimination*: "getting rid of ``destructor terms'' like
  `(CAR X)` and `(CDR X)` by replacing a variable, e.g., `X`, by a
  ``constructor'' term, e.g., `(CONS A B)`";
- *fertilization*: "using an equivalence hypothesis by substituting one side
  for the other in the goal", restricted under induction to one side of the
  conclusion (cross-fertilization), and "used only when generalization is
  enabled";
- *generalization*: "replacing a term by a new variable and restricting the
  new variable to have some of the properties of the term";
- *elimination of irrelevance*: "throwing away unnecessary hypotheses";
- *induction*: "selecting an induction scheme to prove a formula".

A goal that simplification no longer changes is "stable under
simplification", and only then is the next technique tried; "it saves up all
the subgoals for which induction is the only proof technique left to try"
[:doc architecture-of-the-prover]. "Every proof by induction starts a new
trip through the waterfall, as does every forcing round; and these occur only
after all preceding trips through the waterfall are complete"
[:doc hints-and-the-waterfall]. The "preprocess" step uses only rules it
considers fast: rewrite rules and non-recursive definitions that are
"abbreviations", meaning no hypotheses, no loop-stopper, a right side with no
more variable occurrences than the left, and no `if`, `not` or `implies`
[:doc simple].

### 1.5.2 What each process prints

One proof shows every process. `examples/prover/waterfall-rv-rv.lisp` proves
`(implies (true-listp x) (equal (rv (rv x)) x))` for a list reverse `rv` with
no lemma supplied [example: examples/prover/waterfall-rv-rv.lisp]. With
`(set-gag-mode nil)` the narration is, abridged to the lines that name a
process [measured: `(set-gag-mode nil)` then the forms of
examples/prover/waterfall-rv-rv.lisp, laptop REPL, ACL2 8.7 / SBCL 2.6.8]:

```
Perhaps we can prove *1 by induction.  Two induction schemes are suggested
by this conjecture.  Subsumption reduces that number to one.

We will induct according to a scheme suggested by (RV X), while ac-
commodating (TRUE-LISTP X).
...
This simplifies, using the :definitions RV and TRUE-LISTP, to

Subgoal *1/2'
(IMPLIES (AND (CONSP X)
              (EQUAL (RV (RV (CDR X))) (CDR X))
              (TRUE-LISTP (CDR X)))
         (EQUAL (RV (APPEND (RV (CDR X)) (LIST (CAR X))))
                X)).

The destructor terms (CAR X) and (CDR X) can be eliminated by using
CAR-CDR-ELIM to replace X by (CONS X1 X2), (CAR X) by X1 and (CDR X)
by X2.  This produces the following goal.
...
We now use the first hypothesis by cross-fertilizing (RV (RV X2)) for
X2 and throwing away the hypothesis.  This produces
...
We generalize this conjecture, replacing (RV X2) by RV and restricting
the type of the new variable RV to be that of the term it replaces,
as established by RV.  This produces
...
We suspect that the term (TRUE-LISTP X2) is irrelevant to the truth
of this conjecture and throw it out.  We will thus try to prove

Subgoal *1/2'6'
(IMPLIES (TRUE-LISTP RV)
         (EQUAL (RV (APPEND RV (LIST X1)))
                (CONS X1 (RV RV)))).

Name the formula above *1.1.
...
Perhaps we can prove *1.1 by induction.  Three induction schemes are
suggested by this conjecture.  Subsumption reduces that number to two.
These merge into one derived induction scheme.
```

The second induction proves `*1.1`, and with it the theorem. The prover
invented the lemma `(rv (append rv (list x1)))` = `(cons x1 (rv rv))` by
generalizing. That is the good case. The tutorial's warning about the same
processes: "At the two generalization checkpoints -- where hypotheses are
discarded or terms are replaced by variables -- ask yourself whether the
result is a theorem. It often is not" [:doc the-method].

### 1.5.3 Settling down, and the second push

A goal that simplification cannot change has "settled down", and the
settled-down process sends it through the waterfall once more so that later
processes and computed hints can react to that fact
[:doc hints-and-the-waterfall].

When a second goal is pushed for induction the prover, by default, gives up
the work it has done and inducts on the original conjecture instead: "upon
setting aside the second such subgoal, the system chickens out and decides
that rather than prove n>1 subgoals inductively, it will abandon its initial
work and attempt induction on the originally submitted conjecture"
[:doc otf-flg]. The message is

```
Normally we would attempt to prove Subgoal 7.2 by induction.  However,
we prefer in this instance to focus on the original input conjecture
rather than this simplified special case.  We therefore abandon our
previous work on this conjecture and reassign the name *1 to the original
conjecture.  (See :DOC otf-flg.)
```

[measured: the first `thm` of examples/prover/false-conjecture.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. `:otf-flg t` ("Onward Through the Fog") keeps
all the pushed subgoals and tries each by induction; "even when you don't
expect induction to be used or to succeed, setting the `:otf-flg` is a good
way to force the system to generate and display all the initial subgoals"
[:doc otf-flg]. Its default is `t` for `defun` and `verify-termination`, `nil`
otherwise [:doc otf-flg].

### 1.5.4 Turning processes off

The `:do-not` hint names processes not to use "at or below the goal in
question", from the list `preprocess`, `simplify`, `eliminate-destructors`,
`fertilize`, `generalize`, `eliminate-irrelevance` [:doc hints]. The manual's
own advice for a theorem whose generalization goes wrong is to ask "whether
the result is a theorem" and to prove the restricted version as a rewrite
rule [:doc the-method]; `:do-not '(generalize)` is the way to stop the prover
from inventing the generalization while you write that lemma.

## 1.6 Reading a failed proof

### 1.6.1 Key checkpoints and gag mode

"By default, gag-mode is enabled, set to `:goals`" [:doc set-gag-mode].
"Gag-mode focuses attention on so-called ``key checkpoints''. By default, a
checkpoint is a goal that cannot be simplified ... A key checkpoint is a
checkpoint that is not descended from another checkpoint" [:doc set-gag-mode].
With `:goals` the name of each goal is printed as it is produced, and "a key
checkpoint is only displayed when ACL2 is unable to make any further progress
on that goal or some descendant of it, other than with a proof by induction"
[:doc set-gag-mode]; it is printed between `([` and `])` lines, as in the
transcripts below [measured: any failing `thm` of examples/prover/, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. At the
end of a failed proof the key checkpoints are printed again, after the line
the tutorial tells you to look for, "The key checkpoint goals, below, may help
you to debug this failure" [:doc introduction-to-the-theorem-prover].

To see everything gag mode suppressed, `:pso` prints "output that was
generated in an environment where output was being saved, as in gag-mode";
saved output is cleared at every top-level prover call, and `(pso "Subgoal
*1/2''")` prints one goal's output [:doc pso]. `(set-gag-mode nil)` prints the
whole narration as it happens [:doc set-gag-mode]. The number of checkpoints
printed at the end is the `checkpoint-summary-limit`, `(NIL . 3)` by default
as `:checkpoint-summary-limit` shows [:doc checkpoint-summary-limit].

Gag mode prints little about sub-inductions (`*1.1`, `*1.1.2` and so on),
deliberately: "unsuccessful sub-inductions should generally be avoided, not
analyzed for ways to make them succeed. Instead, the key checkpoint that
generated the goal pushed for this induction is more appropriate to analyze
... the ``higher level'' the checkpoint, the more worthy it is of attention"
[:doc set-gag-mode].

### 1.6.2 The Method

The manual's procedure for working through failures is called The Method
(with capitals, "to remind you of this we call this ``The Method'' rather
than ``the method''") [:doc the-method]. Its steps, from that topic:

1. Think about the proof first: induction followed by simplification, or
   simplification alone. Prove the lemmas the proof needs first.
2. Submit the theorem; "Abort the proof if it runs more than a few seconds."
3. If it succeeded, move on.
4. "Otherwise, inspect the failed proof attempt, starting from the beginning,
   not the end. Basically you should look for the first place the proof
   attempt deviates from your imagined proof. If your imagined proof was
   inductive, inspect the induction scheme used by ACL2. If that is ok, then
   find the first subsequent subgoal that is stable under simplification and
   think about why it was not proved by the simplifier."

The tutorial's companion list of questions at a key checkpoint
[:doc introduction-to-key-checkpoints], condensed:

1. Do you believe this formula is a theorem?
2. Can it be simplified, by a simpler fact about a few of its function
   symbols?
3. Is that simpler fact already in the database? If so, why was it not
   used: (3a) it is disabled; (3b) "its left-hand side doesn't match the
   target"; (3c) "it is an `IFF` rule but the target doesn't occur
   propositionally"; (3d) "the hypotheses of the rule cannot be relieved for
   this occurrence of the target".
4. If not, prove it, as a rule.
5. Otherwise, is this a formula you would prove by induction, and is it
   general enough for induction to work?
6. Did ACL2 induct? If not, why not?
7. If it did, was it the right induction?
8. If the post-induction checkpoints look plausible, ask the same questions
   of each.

And after any repair: "**Start over trying to prove your main conjecture.**
... Do not just scroll back to the key checkpoints generated the last time"
[:doc introduction-to-key-checkpoints].

### 1.6.3 Reading the clause

A checkpoint is printed as an `IMPLIES` but is a clause, "a list of terms
that is implicitly viewed as a disjunction"; `(implies (and p q) r)` is most
likely the clause `((not p) (not q) r)` [:doc clause-processor]. What is
printed is the goal after rewriting, so the hypotheses are in the normal form
the rules produced, not as you typed them. `(natp n)` in the conjecture of
`examples/prover/induct-hint.lisp` arrives at its checkpoint as
`(INTEGERP N) (<= 0 N)`:

```
Goal''
(IMPLIES (AND (INTEGERP N) (<= 0 N))
         (EQUAL (+ 1 (LEN (TK N (CDR X))))
                (+ 1 N)))
```

[measured: the first `thm` of examples/prover/induct-hint.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. The definition of `natp` was
opened (`(:DEFINITION NATP)` is in the `Rules:` list of the same summary)
[measured: same run].

Three things to look for in a clause:

- **A term you expected a rule to rewrite.** "Look for signs that your
  existing rules did not apply, e.g., for terms that should have been
  rewritten, and figure out why they were not. Possible causes include that
  they do not exactly match your old rules, that your old rules have
  hypotheses that cannot be relieved here ... or perhaps your old rules are
  disabled" [:doc the-method]. Questions (3a) to (3d) above, and the
  break-rewrite tools of section 1.7.4, find which.
- **Contradictory hypotheses.** "the checkpoint might contain the two
  hypotheses `(P (F A))` and `(NOT (Q (G (F A))))` and you might realize that
  `(implies (p x) (q (g x)))` is a theorem" [:doc the-method]; after an
  induction, look for `(MEMBER e x)` beside `(NOT (MEMBER e' x'))` with `e`,
  `e'` and `x`, `x'` possibly equal [:doc post-induction-key-checkpoints].
- **`HIDE`.** "terms of the form `(hide x)` are ignored by the ACL2 rewriter,
  except when explicit `:expand` hints are given for such terms ... or when
  rewrite rules explicitly about `hide` are available" [:doc hide]. The
  simplifier inserts it in two situations: equality heuristics apply it to an
  equality after substituting it into the rest of the goal, and an attempted
  ground evaluation failed, typically because it reached a constrained
  function; then it inserts `(hide (comment "Failed attempt to call
  constrained function ..." ...))` [:doc hide]. In the second case `:expand`
  does not help ("the execution will just fail again"); disabling the
  executable counterpart of the function does [:doc hide].

The case analysis of a checkpoint is reported with its causes. A summary like

```
Splitter note (see :DOC splitter) for Goal (9 subgoals).
  if-intro: ((:DEFINITION NFIX))
```

[measured: the first `thm` of examples/prover/false-conjecture.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8] names the rule applications that may have
introduced an `IF` and so split the goal; `case-split` and `immed-forced` are
the other kinds, and splits caused by `IF` already in the goal are not
reported [:doc splitter]. How many cases the simplifier will produce before it
stops rewriting further literals is `case-split-limitations`, `(500 100)` by
default [:doc case-split-limitations].

### 1.6.4 When the goal is false

"Each post-induction key checkpoint is a theorem if and only if the original
conjecture was a theorem ... So if you see a post-induction key checkpoint
that is not a theorem, stop looking at the checkpoints! Your original
conjecture is not a theorem! Fix it" [:doc post-induction-key-checkpoints].
The reason given, "simplification preserves equivalence"
[:doc post-induction-key-checkpoints], applies as well to a checkpoint the
simplifier produced from the goal before any induction. It does not apply
after generalization or elimination of irrelevance, which discard information:
"ask yourself whether the result is a theorem. It often is not"
[:doc the-method].

`examples/prover/false-conjecture.lisp` is a real instance. With

```lisp
(defun tk (n x)
  (if (zp n)
      nil
    (cons (car x) (tk (1- n) (cdr x)))))
```

the conjecture `(equal (tk n (tk m x)) (tk (min (nfix n) (nfix m)) x))`
fails, and among its key checkpoints is

```
Subgoal 8'
(IMPLIES (AND (INTEGERP N)
              (<= 0 N)
              (NOT (INTEGERP M)))
         (NOT (TK N NIL)))
```

[measured: the first `thm` of examples/prover/false-conjecture.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. `(tk 1 nil)` is `(nil)`, so the checkpoint is
false, and so is the conjecture. Evaluation confirms it before any more
proving:

```lisp
(assert-event (equal (tk 2 (tk 0 '(a b))) '(nil nil)))
(assert-event (not (equal (tk 2 (tk 0 '(a b)))
                          (tk (min 2 0) '(a b)))))
```

and the corrected statement, which restricts `n` to at most `m`, proves
without hints [example: examples/prover/false-conjecture.lisp]. The habit to
take from this: evaluate the conjecture on a few small constants, including
the non-list, zero and short-list cases that totality admits, before reading
any checkpoint closely. `assert-event` is the form that puts such a check in a
book (chapter 2).

### 1.6.5 When the statement is too weak, and when a lemma is missing

**Too specific to induct on.** The accumulator version of reverse,

```lisp
(defun rva (x acc)
  (if (consp x)
      (rva (cdr x) (cons (car x) acc))
    acc))
```

does not let ACL2 prove `(equal (rva x nil) (rv x))`. The key checkpoint
under the induction says why:

```
*** Key checkpoint under a top-level induction: ***

Subgoal *1/1'
(IMPLIES (AND (CONSP X)
              (EQUAL (RVA (CDR X) NIL) (RV (CDR X))))
         (EQUAL (RVA (CDR X) (LIST (CAR X)))
                (APPEND (RV (CDR X)) (LIST (CAR X)))))
```

[measured: `(thm (equal (rva x nil) (rv x)))` after the defuns of
examples/prover/induction-accumulator.lisp, laptop REPL, ACL2 8.7 / SBCL
2.6.8]. The hypothesis is about accumulator `NIL`, the conclusion about
accumulator `(LIST (CAR X))`. This is the tutorial's question 5: "in an
inductive proof, the main thing you have to work with is the induction
hypothesis, which is an instance of the theorem you're proving. If the theorem
is not general enough, you won't be able to assume an instance that will help
you" [:doc introduction-to-key-checkpoints]. The repair is the general
theorem for every accumulator, `(equal (rva x acc) (append (rv x) acc))`,
which ACL2 proves unaided; the special case is then a rewrite away
[example: examples/prover/induction-accumulator.lisp].

**A lemma, not an induction.** `(equal (drop i (drop j x)) (drop j (drop i
x)))` for naturals `i`, `j` is attacked by the merged induction shown in
section 1.4.2 and fails in sub-inductions. Nothing is wrong with the
induction; the database lacks the fact that nested `drop` is one `drop`. With
`drop-of-drop` proved (by induction on `j`), both sides rewrite to
`(drop (+ i j) x)` and the theorem needs no induction at all
[example: examples/prover/induction-lemma-first.lisp]. This is the tutorial's
question 2, "Is there some combination of function symbols in it that could
be eliminated or simplified by exploiting some simpler fact?", asked before
question 5 [:doc introduction-to-key-checkpoints].

The tutorial's advice on generalizing a checkpoint applies to both:
"(1) look for simplifiable combinations of function symbols within
propositional components, (2) look for relations between propositional
components, and (3) throw out irrelevant or weakly connected components"
[:doc generalizing-key-checkpoints].

### 1.6.6 The summary: `Rules:`, `Time:`, `Prover steps counted:`

Every event ends with a summary. Its fields are `Form`, `Rules` ("Runes
contributing to the proof or storage of the event"), `Hint-events`,
`Splitter-rules`, `Warnings`, `Time` and `Prover steps counted`
[:doc summary]. For the failed `:use` attempt of section 1.8.2 it reads

```
Summary
Form:  ( THM ...)
Rules: ((:EXECUTABLE-COUNTERPART NOT)
        (:REWRITE CAR-P))
Hint-events: ((:USE CAR-P))
Warnings:  Use
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
Prover steps counted:  85
```

[measured: the failing `thm` of examples/prover/use-instance.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. `(:REWRITE CAR-P)` in `Rules:` is the
self-defeat of that hint, visible in two lines.

**Read `Time:` before the subgoals.** fn's measurement:

```
Time:  2386.26 seconds (prove: 0.02, print: 0.00, other: 2386.24)
```

for `fn-tcl-drive-partition-independence` in `books/tcpcl-invariants`: "Forty
minutes, and the prover did two hundredths of a second of proof search. The
cure for that shape is a **theory change, not a hint**"
[fn: docs/proof-style.md:591 @3bbfc4dca]. fn's document says "`other` is
where forward chaining and type reasoning go", and the lane that read the
splitter note instead of this line lost most of its budget, twice
[fn: docs/proof-style.md:593 @3bbfc4dca]. The mechanism that profiling then
named was a second whole-state recognizer exported with its own rule family,
which doubled the forward-chaining work on every goal that opened the
transition [fn: docs/proof-style.md:607 @3bbfc4dca]. The opposite shape,
`prove` large and steps few, fn found to be the tau system or a library's
`syntaxp`/`bind-free` tests, neither of which counts as prover steps or
appears as frames; it tested that by disabling `(tau-system)` after the
includes and comparing [fn: docs/proof-style.md:621 @3bbfc4dca].

**Prover steps** are ACL2's own count: "Currently, a step is counted for each
call of the system functions `rewrite` and `expand-abbreviations`. However,
the steps counted may change in future releases" [:doc set-prover-step-limit].
fn uses the count, not wall time, as its regression ratchet, because "for
fixed bytes and toolchain the count is the same on any box at any load"
[fn: docs/proofs.md:117 @3bbfc4dca].

## 1.7 Tools for looking inside a proof

### 1.7.1 `accumulated-persistence`

"Generally speaking, the more ACL2 knows, the slower it runs ... the system
tries to apply rules that you have forgotten were even there"; accumulated
persistence "is a statistic ... that helps you identify the rules that are
causing ACL2's search space to explode" [:doc accumulated-persistence]. The
forms:

```lisp
(accumulated-persistence t)           ; start, clearing old statistics
(thm ...)                             ; the proof under study
(show-accumulated-persistence :frames)
(accumulated-persistence nil)         ; stop
```

[:doc accumulated-persistence]. The accumulated persistence of a rune is the
number of rune applications attempted while it was being tried, itself
included; a try that fails, and everything done on its behalf, is "useless"
[:doc accumulated-persistence]. "A large number of ``useless'' `:frames` or
`:tries` along with correspondingly small ``useful'' counts may suggest runes
to consider disabling" [:doc accumulated-persistence]. On the failed
`drop`-commutes attempt it reports

```
Accumulated Persistence (694 :tries useful, 2062 :tries not useful)
   :frames   :tries    :ratio  rune
   --------------------------------
      1838      284 (    6.47) (:DEFINITION DROP)
       146       39    [useful]
      1692      245    [useless]
   --------------------------------
       680      332 (    2.04) (:REWRITE ZP-OPEN)
        12        3    [useful]
       668      329    [useless]
```

[measured: `(accumulated-persistence t)`, the failing `thm` of
examples/prover/induction-lemma-first.lisp, `(show-accumulated-persistence
:frames)`, laptop REPL, ACL2 8.7 / SBCL 2.6.8]. Most of the work went into
opening `drop` uselessly, which is what a missing `drop-of-drop` lemma looks
like from inside. Two cautions from the manual: a high-persistence rune "may
not actually be the ``culprit''" (it may be billed for another rune's work),
and after an aborted proof only completed tries are counted unless you ask
for `:frames-a` or `:tries-a` [:doc accumulated-persistence]. Turning it on
costs time; the manual measured "approximately 11% more time" in a full
regression [:doc accumulated-persistence]. `(accumulated-persistence :all)`
adds per-hypothesis statistics [:doc accumulated-persistence].

fn made this the first thing to run on a slow form: `tools/proof_profile.py`
builds a driver from the book's own source up to the form, runs it under
`(accumulated-persistence t)` with a step limit, and prints the useless-frame
fan, the top rules by frames and by tries, the summary and the first key
checkpoint [fn: docs/proof-style.md:561 @3bbfc4dca]. "A lane that reaches for
`minimal-theory` instead has skipped this step"
[fn: docs/proof-style.md:588 @3bbfc4dca].

### 1.7.2 `dmr`

`dmr` watches the rewriter "in real time": an ACL2 component writes a file,
and an Emacs component displays it in a buffer; `(dmr-start)` and
`(dmr-stop)` turn the ACL2 side on and off [:doc dmr]. Each line of the
display is an activity leading to the one below it; "a line that persists for
awhile without a leading asterisk can suggest why the proof is taking a long
time" [:doc dmr]. It needs Emacs and ACL2 on the same machine, because the
file is under `/tmp` [:doc dmr].

### 1.7.3 `pstack`

"When the form `(pstack)` is executed during a break from a proof, or at the
end of a proof that the user has aborted, a ``process stack'' ... will be
printed that gives some idea of what the theorem prover has been doing"; its
entries are the waterfall processes (`simplify-clause` and so on) and
subroutines such as `ev-fncall` (evaluating a function on explicit
arguments), `forward-chain` and `induct` [:doc pstack].

### 1.7.4 Break-rewrite: `:brr`, `:monitor`, `:eval`, `cw-gstack`

The rewriter can stop at a monitored rule. "The basic protocol is that you
turn on the break-rewrite utility with `brr` and then you use this facility,
`monitor`, to specify the rules you want to monitor" [:doc monitor]:

```lisp
:brr t
:monitor (:rewrite assoc-of-app) t
(thm ...)               ; breaks when the rule is tried
```

Inside a break, `:target` is the term being rewritten, `:unify-subst` the
substitution, and `:path` "the stack of goals pursued by the rewriter";
`:ok` and `:go` proceed (`:go` printing the outcome), and `:eval` tries the
rule and returns to the break with the result, after which
`:failure-reason` says why a rule did not apply [:doc break-rewrite]. `:a!`
aborts [:doc break-rewrite]. A break cannot change the proof: it runs in a
"wormhole", a copy of the state that is discarded when the break exits
[:doc break-rewrite]. The rewriter "performs more sluggishly" while `brr` is
on, so turn it off with `:brr nil` when done [:doc break-rewrite].

A rule pattern that fails to match can still cause a break if the monitor
asks for near misses, with `:depth n`, `:abstraction pat` or `:lambda t`
[:doc monitor]. If a monitored rule never breaks, the manual's list of likely
reasons is: `brr` is off; the rune is disabled at that subgoal; the rule is
an abbreviation tried only in preprocessing (give `:do-not '(preprocess)`);
`:hands-off` names its function; the only targets were inside a `HIDE`; or
no target with that function symbol was ever rewritten [:doc monitor].

`cw-gstack` prints the rewriter's stack "when a proof is interrupted
(because of control-c or because of a loop)", provided `brr` is on
[:doc cw-gstack]. Chapter 2 shows it on a real loop: the frames alternate
between two rules applied to the same term
[example: examples/rewriting/loop-pair.lisp].

### 1.7.5 History: `:pe`, `:pl`, `:pr`, `:pbt`, `:ubt`

- `:pe name` prints the event that introduced `name`, with the command it was
  part of [:doc pe].
- `:pl` takes a function symbol or a term and lists the rules that apply to
  it, newest first, with the hypotheses that remain after simple attempts to
  discharge them [:doc pl].
- `:pr name` prints the rules an event stored, with each rune's enabled
  status [:doc pr].
- `:pbt` prints the commands back through a command descriptor; `:ubt` undoes
  them, and undoes whole command blocks, not single events [:doc pbt],
  [:doc ubt].

For the looping pair of chapter 2, `:pl (f1 a)` lists the rewrite rule, the
disabled definition and the type prescription that could apply:

```
(:REWRITE F1-IS-F2)
  New term: (F2 A)
  Hypotheses: ((CONSP A))
  Equiv: EQUAL
  Substitution: ((X A))
(:DEFINITION F1) (disabled)
  New term: (CONS A 1)
  Hypotheses: <none>
  Equiv: EQUAL
  Substitution: ((X A))
```

[measured: `:pl (f1 a)` after the events of examples/rewriting/loop-pair.lisp
up to `f2-is-f1`, laptop REPL, ACL2 8.7 / SBCL 2.6.8]. `:pl` shows rules that
are *possibly* applicable; heuristics such as loop-stoppers and failed
hypotheses may still stop them [:doc pl].

### 1.7.6 A live session against certified dependencies

fn's `tools/proof_repl.py` keeps one ACL2 alive behind a socket, loads a book
up to a named event against the certified closure, and wraps each sent event
in `with-prover-time-limit`, so that "a search that stops returning costs a
minute, not the session"; its answers carry ACL2's own `Time:` and step count
[fn: docs/proofs.md:489 @3bbfc4dca]. "A form ACL2 admits there is not a
certificate; the event goes into the book and the book certifies"
[fn: docs/proofs.md:506 @3bbfc4dca]. This guide's REPL equivalent is a file
of forms piped into the launcher under `timeout`.

## 1.8 Hints

### 1.8.1 Where hints go, and which are inherited

"Hints are allowed in all events that use the theorem prover. During `defun`
events there are two different uses of the theorem prover: one to prove
termination and another to verify the guards"; use `:hints` in `xargs` for
the first and `:guard-hints` for the second [:doc hints]. The general form is
a list of `(goal-spec :key1 val1 ...)` entries [:doc hints]. A goal-spec is
the goal's name as printed, in a string, matched case-insensitively but
otherwise exactly: `"Subgoal *1/3.2'"`, `"[1]Subgoal *1/3.2'"`; "If there is
no such match, then the hint is ignored" [:doc goal-spec]. Copy the name from
the output.

"The first hint of the form `("G" :kwd1 val1 ...)` is applied to that goal",
and later ones for the same goal are ignored with a warning [:doc hints].
Duplicate keywords in one hint are illegal, as are some combinations, such as
`:use` with `:induct` [:doc hints].

Most hints, once selected for a goal, stay in force for its descendants. "The
following hints, however, have a specific effect only on the goal to which
they are applied: `:bdd`, `:by`, `:cases`, `:clause-processor`, `:error`,
`:induct`, `:or`, and `:use`" [:doc hints]. The waterfall keeps a list of
"hint settings" passed from goal to children and re-applied at the start of
an induction proof, and `:use`, `:cases`, `:by`, `:bdd`, `:or` and
`:clause-processor` "are never saved in the hint settings"
[:doc hints-and-the-waterfall].

The best-practices advice on all of this: "Try to avoid subgoal hints. These
can make proofs brittle and difficult to maintain. If it is not sufficient to
apply hints to the top-level goal, consider factoring out a subgoal into an
auxiliary lemma", and "the less hints for a proof, the better"
[:doc best-practices].

### 1.8.2 `:use`, `:instance`, `:functional-instance`

**Pitfall.** `:use` "replaces a goal, `G`, by the new goal, `(IMPLIES P G)`,
where `P` is the theorem specified by the (conjunction of the) lemma
instances provided" [:doc hints]. The instance is a *hypothesis*, and "these
new hypotheses participate fully in all subsequent rewriting" [:doc hints].
So if the lemma is also an enabled rewrite rule, the rewriter reduces the
hypothesis to `T` and it is gone. ACL2 warns:

```
ACL2 Warning [Use] in ( THM ...):  It is unusual to :USE the formula
of an enabled :REWRITE or :DEFINITION rule, so you may want to consider
disabling (:REWRITE CAR-P) in the hint provided for Goal.  See :DOC
using-enabled-rules.
```

[measured: the failing `thm` of examples/prover/use-instance.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. The shape to copy keeps the hypotheses by
disabling the rule in the same hint [:doc using-enabled-rules]:

```lisp
(defthm p-injective
  (implies (equal (p x1) (p x2))
           (equal x1 x2))
  :hints (("Goal" :use ((:instance car-p (x x1))
                        (:instance car-p (x x2)))
                  :in-theory (disable car-p))))
```

[example: examples/prover/use-instance.lisp].

The lemma instances `:use` takes [:doc lemma-instance]:

- a name, meaning the theorem (or the normalized body of a defined function);
- a rune, meaning its corollary;
- `(:theorem term)`, a term ACL2 must first prove;
- `(:instance lmi (v1 t1) ... (vn tn))`, an instance; "each `vi` must be
  bound in `F`" unless `:extra-bindings-ok` follows the lemma;
- `(:functional-instance lmi (f1 g1) ... (fn gn))`, replacing function
  symbols, at the price of proving the replaced functions' constraints
  (chapter 2 has the certified example,
  [example: examples/books/encapsulate-fi.lisp]);
- `(:termination-theorem fn)` and `(:guard-theorem fn)`.

A lemma meant only for `:use` is stored with `:rule-classes nil`, so it adds
no rule and changes no later proof: `examples/prover/rule-classes-nil-use.lisp`
fails a goal that needs the fact, then proves it with
`:use ((:instance mag-bound (x y)))` [example:
examples/prover/rule-classes-nil-use.lisp]. That is fn's rule for guard-proof
equalities: "An equality that exists to discharge a guard or an `mbe`
obligation is not a rewrite rule. It is stated once, `:rule-classes nil`, and
used by `:use`" [fn: docs/proof-style.md:242 @3bbfc4dca].

### 1.8.3 `:cases`

"For each term in the list, a new goal is created from the current goal by
assuming that term; and also, in essence, one additional new goal is created
by assuming all the terms in the list false" [:doc hints]. Use it when the
rules you need have hypotheses about a condition the goal does not mention.
In `examples/prover/cases-hint.lisp`, `mag` has one rule for negative
arguments and one for non-negative ones; `(<= 0 (mag x))` fails because
neither hypothesis can be relieved, and `:cases ((< x 0))` gives each case
the fact its rule needs [example: examples/prover/cases-hint.lisp]:

```lisp
(defthm mag-non-negative
  (implies (rationalp x)
           (<= 0 (mag x)))
  :hints (("Goal" :cases ((< x 0)))))
```

`:cases` splits immediately, "without calling the ACL2 rewriter", and is not
inherited [:doc hints].

### 1.8.4 `:expand`

`:expand` lists calls to open "when they are encountered by the simplifier
while working on the specified goal or any of its subgoals"; `(:free (vars)
pattern)` opens every instance of a pattern, `(:with name term)` opens with a
named definition or rewrite rule, and `:lambdas` opens every `let`
[:doc hints]. The rewriter's own heuristics decide which calls to open
[:doc defun], and they sometimes decline a call you need.
`(equal (len (tk 1 x)) 1)` fails with "No induction schemes are suggested",
because `(tk 1 x)` is not opened; `:expand ((tk 1 x))` proves it
[example: examples/prover/expand-hint.lisp]:

```lisp
(defthm len-of-tk-1
  (equal (len (tk 1 x)) 1)
  :hints (("Goal" :expand ((tk 1 x)))))
```

`:expand` is also the only way, besides rules about `hide`, to open a `HIDE`
term: `:expand ((:free (x) (hide x)))` [:doc hide].

### 1.8.5 `:induct`

"`Value` is either `t` or a term that is not an atom or a quoted constant.
The value `t` indicates that the system use induction immediately ...
Otherwise, the system should apply induction immediately, but it should
analyze `value` rather than the goal to generate its induction scheme"
[:doc hints]. Merging still applies, so `(list (nth i a) (nth j a))`
"suggests simultaneous induction on `i`, `j`, and `a`" [:doc hints]. To get
the same behaviour the prover chose by itself, include the suggesting term and
every accommodated term: `:induct (list term0 term1 ... termk)` [:doc hints].
An `:induct` hint on a subgoal goes on the subgoal's name, not on the `*1.1`
name it is given when pushed [:doc goal-spec]. Section 1.9 has the examples.

### 1.8.6 `:in-theory`: `enable`, `disable`, `e/d`

`:in-theory` takes a theory expression, "evaluated relative to the current
ACL2 logical world, not relative to the theory of a previous goal"
[:doc hints]. `(enable a b)`, `(disable a b)` and `(e/d (enables) (disables)
...)` are the usual expressions [:doc enable], [:doc disable], [:doc e/d];
chapter 2 describes theories in full.

**Pitfall: a `Goal` `:in-theory` does not survive a subgoal that has its
own.** The manual's example [:doc hints]:

```lisp
(defthm prop
  (p (f (g x)))
  :hints (("Goal"      :in-theory (disable f))
          ("Subgoal 3" :in-theory (enable  g))))
```

"This call of the `enable` macro enables `g` relative to the `current-theory`
of the current logical world, *not* relative to the theory produced by the
hint at `Goal`. Thus, the `disable` of `f` on behalf of the hint at `Goal`
will be lost at `Subgoal 3`" [:doc hints]. fn paid for this in
`books/tcpcl-invariants`: a `Goal` hint disabled `fn-tcl-step` and a subgoal
hint `(enable fn-tcl-drive-is-a-result)` put it back under every subgoal of
the fold; closing the four transitions once, at the top of the book, "took C1
from 0.42 s to 0.05 s and the whole book from 609.53 s to 6.54 s"
[fn: docs/proof-style.md:673 @3bbfc4dca]. fn's two consequences: "To hold
everywhere, close it in the book, not in a `Goal` hint", and "A subgoal hint
that means 'the Goal's theory plus this' must spell the whole `e/d` again"
[fn: docs/proof-style.md:700 @3bbfc4dca].

`examples/prover/subgoal-theory.lisp` makes the effect visible. A `Goal`
hint disables `f` and its executable counterpart and splits with `:cases`;
the proof fails, because both cases inherit the disable. Add
`("Subgoal 2" :in-theory (enable gg))` and the same for `Subgoal 1`, about an
unrelated function `gg`, and the proof *succeeds*: each subgoal's theory is
the global theory plus `gg`, in which `f` is enabled. Spelling the whole theory
at each subgoal, `(e/d (gg) (f (:e f)))`, makes it fail again, as it should
[example: examples/prover/subgoal-theory.lisp].

### 1.8.7 `:do-not` and `:do-not-induct`

`:do-not` turns off waterfall processes at and below the goal (section
1.5.4) [:doc hints]. `:do-not-induct t` makes the prover fail as soon as it
would push a goal for induction under the named goal; with `:otf-flg t` it
continues to the end first; a non-keyword symbol value instead skips each
such goal and prints it as an event to prove [:doc hints]. An `:induct` hint
overrides `:do-not-induct` on its own goal [:doc hints]. As a probe it answers
"does simplification alone do this?" quickly:
`examples/prover/step-limits.lisp` fails the accumulator theorem under
`:do-not-induct t` and then proves it without the hint
[example: examples/prover/step-limits.lisp].

### 1.8.8 `:nonlinearp`

"`Value` is `t` or `nil`, indicating whether non-linear-arithmetic is
active. The default value is `nil`" [:doc hints]. Linear arithmetic treats a
product of unknowns as an unknown; `(implies (and (rationalp x) (rationalp
y) (< 1 x) (< 1 y)) (< 1 (* x y)))` fails without the hint and proves with
`:nonlinearp t` [example: examples/prover/nonlinearp.lisp].
`(set-non-linearp t)` turns it on for subsequent events and is local to the
book [:doc set-non-linearp]. When it is on, "the conclusions are rewritten
under a different theory than under ``normal'' rewriting", which is why its
own topic proves helper rules about `*` first [:doc non-linear-arithmetic].

### 1.8.9 `:by`

`:by` says the goal "is either equal to the proposition denoted by the
instance, or is subsumed by that proposition when both are viewed as
clauses" [:doc hints]. No search is done. In
`examples/prover/by-and-restrict.lisp` a theorem that is `drop-of-drop` with
renamed variables is proved by `:by drop-of-drop`
[example: examples/prover/by-and-restrict.lisp]. `:by nil` gives a goal a
"bye": it is skipped, and at the end the prover prints the `defthm`s that
would complete the proof, which is a way to work top-down [:doc hints]. A
proof that used it is not a proof until those events are proved.

### 1.8.10 `:restrict`

`:restrict` limits the substitutions a `:rewrite` or `:definition` rule may
use, which "sometimes allows rules with free variables ... to be applied
successfully by the rewriter, thus avoiding the clutter, case-splitting, and
theory management (disabling) that can occur with `:use` hints"
[:doc hints]. The substitutions "refer to the variables actually appearing in
the goals"; restrict hints are ignored by the preprocessor [:doc hints]. The
manual's example, certified in `examples/prover/by-and-restrict.lisp`: with
`subsetp-trans` (free variable `y`) and `subsetp-evens`,
`(subsetp (evens (evens l)) l)` fails, and

```lisp
:hints (("Goal" :restrict ((subsetp-trans ((y (evens l)))))))
```

proves it [:doc hints], [example: examples/prover/by-and-restrict.lisp].

### 1.8.11 `:clause-processor`

A clause processor is "a simplifier at the level of goals", a function from a
clause to a list of clauses; a verified one is justified by a theorem of rule
class `:clause-processor` stated with an evaluator from `defevaluator`, and is
applied only by explicit `:clause-processor` hints [:doc clause-processor].
`examples/prover/clause-processor.lisp` certifies the manual's
`note-fact-clause-processor`, which replaces a goal by the goal with a fact
added as a hypothesis and the fact itself, and uses it to finish a proof that
fails without it [example: examples/prover/clause-processor.lisp]. The term
in the hint must be translated: the first attempt of this guide passed
`'(<= 0 (mag y))` and ACL2 refused it with "did not evaluate to a list of
clauses"; the translated form is `'(not (< (mag y) '0))` [measured: the
`:clause-processor` hint of examples/prover/clause-processor.lisp with the
untranslated term, laptop REPL, ACL2 8.7 / SBCL 2.6.8]. Unverified ("trusted")
clause processors exist too: they are introduced with
`define-trusted-clause-processor`, whose `:ttag` argument generates a
`defttag` event [:doc define-trusted-clause-processor].

### 1.8.12 Computed hints and default hints

A computed hint is a term over the variables `ID`, `CLAUSE`, `WORLD`,
`STABLE-UNDER-SIMPLIFICATIONP`, `HIST`, `PSPV`, `CTX` and `STATE`, evaluated
at every subgoal; it returns `nil` (no hint) or a keyword/value list used "as
though the user had typed them explicitly" [:doc computed-hints].
`stable-under-simplificationp` is `t` "only if the clause is known to be
stable under simplification"; "it is frequently useful to inject hints (e.g.,
to enable a rule or provide a `:use` hint) only when the goal in question has
stabilized" [:doc computed-hints]. The shape to copy
[example: examples/prover/computed-hints.lisp]:

```lisp
:hints ((and stable-under-simplificationp
             '(:in-theory (enable mag))))
```

By default the computed hint is removed from the hints passed to the
subgoal's children; `:computed-hint-replacement t` keeps it
[:doc computed-hints].

`set-default-hints` appends hints "to the right of any explicitly provided
`:hints`" of every later `defthm`, `thm` and `defun`, and "is local to the
book or `encapsulate` form in which it occurs"; `set-default-hints!` exports
it [:doc set-default-hints]. Since explicit hints come first, "An explicit
"Goal" hint would ... take priority" [:doc set-default-hints]. The second
theorem of `examples/prover/computed-hints.lisp` is proved by a default hint
[example: examples/prover/computed-hints.lisp].

### 1.8.13 The rest

`:or` tries several hint lists on a goal in turn [:doc hints]; `:hands-off`
names functions whose calls are not rewritten (their arguments still are)
[:doc hints]; `:backchain-limit-rw` limits backchaining for a goal and its
descendants [:doc hints]; `:case-split-limitations` overrides that setting
[:doc hints]; `:no-thanks t` suppresses the "[Note: A hint was supplied ...
Thanks!]" message [:doc hints]; `:instructions` runs proof-builder
instructions [:doc hints]. `:backtrack` evaluates a computed hint *after* a
process applies, and can reject that process's result
[:doc hints].

## 1.9 Induction schemes in practice

### 1.9.1 Supplying a scheme with `:induct`

One cause of "No induction schemes are suggested" is that the controlling
argument of every recursive call in the goal is a non-variable term, since a
call suggests an induction "only if the controlling actuals are distinct
variables" [:doc induction]. In
`examples/prover/induct-hint.lisp` the goal

```lisp
(implies (natp n) (equal (len (tk (+ 1 n) x)) (+ 1 n)))
```

has `(tk (+ 1 n) x)`, whose controlling argument is `(+ 1 n)`, and `len` of a
non-variable; the prover reports

```
No induction schemes are suggested by *1.  Consequently, the proof
attempt has failed.
```

[measured: the first `thm` of examples/prover/induct-hint.lisp, laptop REPL,
ACL2 8.7 / SBCL 2.6.8]. The repair names a term that recurs the right way,
`:induct (tk n x)`; the base case then needs `(tk 1 x)` opened, so the hint
also says `:expand ((tk 1 x))` [example: examples/prover/induct-hint.lisp]. A
function written only to be named in `:induct` is the general tool: any
admissible recursion is an induction scheme [:doc
logic-knowledge-taken-for-granted-inductive-proof].

The better repair in that book is the general lemma
`(equal (len (tk n x)) (nfix n))`, which ACL2 proves by the induction `(tk n
x)` suggests, after which the special case needs no hint at all
[example: examples/prover/induct-hint.lisp]. An `:induct` hint is a
statement about one goal; a lemma is a rule every later goal can use.

A wrong `:induct` hint can break a proof that would have succeeded. While
writing these examples, the true theorem
`(implies (and (natp i) (natp n) (< i n)) (equal (nth i (tk n x)) (nth i x)))`
proved unaided by the scheme ACL2 chose ("suggested by (NTH I (TK N X))"),
and failed when given `:induct` of a function that decremented `i` and `n`
together with base case `(or (zp i) (zp n))` [measured: the two `thm` forms
on that statement, with and without the hint, after the `tk` defun, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. Try without the hint first.

### 1.9.2 Accommodation and merging

The prover's message names the term whose scheme it uses and the terms it
accommodates (section 1.4.2). When it merged schemes and the proof still
failed, read the scheme it printed: "If you determine the wrong induction was
done, extend ACL2's induction analysis or tell it which induction to do"
[:doc introduction-to-key-checkpoints]. The `:induction` rule class (chapter
2) is the way to extend the analysis: it links a pattern to a scheme, with no
proof obligation [:doc induction].

### 1.9.3 Mutual recursion: `tools/flag`

For a clique defined by `mutual-recursion` the prover suggests no induction:
in `examples/prover/mutual-recursion-flag.lisp`, `(thm (equal (tcopy x) x))`
fails with "No induction schemes are suggested" [example:
examples/prover/mutual-recursion-flag.lisp]. `make-flag` from the community
book `tools/flag` introduces "a ``flag function'' that mimics a
mutual-recursion", a theorem relating it to the clique, and "a macro for
proving properties by induction according to the flag function"
[books: tools/flag.lisp:93]. The shape to copy:

```lisp
(include-book "tools/flag" :dir :system)

(make-flag tcopy)                 ; defines FLAG-TCOPY and DEFTHM-FLAG-TCOPY

(defthm-flag-tcopy
  (defthm tcopy-is-identity
    (equal (tcopy x) x)
    :flag tcopy)
  (defthm lcopy-is-identity
    (equal (lcopy l) l)
    :flag lcopy))
```

[example: examples/prover/mutual-recursion-flag.lisp]. The macro's induction
"only works if you're using the formals of the flag function as the variable
names in the theorems" [books: tools/flag.lisp:93].

## 1.10 Step limits and time limits

`(set-prover-step-limit n)` limits the prover steps of each subsequent event;
it sets the `acl2-defaults-table` and so is local to a book or `encapsulate`;
the limit applies to compound events as a whole, so steps spent by earlier
events inside an `encapsulate` are not available to later ones
[:doc set-prover-step-limit]. `(with-prover-step-limit n form)` limits one
form; steps used inside an inner `with-prover-step-limit` are still charged to
the enclosing limit, unless the inner call is given the extra argument `t`
[:doc with-prover-step-limit]. `(with-prover-time-limit time form)` aborts a
proof that runs past `time` seconds of CPU time by default, and an inner limit
cannot push the deadline later unless it is written as a list
[:doc with-prover-time-limit]. Step limits are "platform-independent", time
limits "generally less restrictive for faster processors"
[:doc with-prover-time-limit], and the community's practice is to "Avoid short
proof timeout windows which could fail on slower machines ... If possible,
avoid timeout windows altogether, or use step limits instead"
[:doc best-practices].

**Pitfall: an aborted probe measures nothing.** "An `ACL2 Error [Step-limit]`
says the form did not finish inside `n`; it says nothing about whether the
form closes, how it splits, or whether the change under test helped -- and
the control run aborts in the same place for the same reason, so a comparison
between them is not a comparison at all"
[fn: docs/proof-style.md:650 @3bbfc4dca]. fn retracted a finding that rested on such a pair, both runs
having hit a 3,000,000-step limit [fn: docs/proof-style.md:659 @3bbfc4dca].
fn's rule: "a `yes` is evidence while a `no` is not. To compare two
configurations, or to locate a split, run without a limit under a wall-clock
`timeout` and read the `Time:` line ... and the profile"
[fn: docs/proof-style.md:666 @3bbfc4dca]. `examples/prover/step-limits.lisp`
records a 100-step abort of a theorem that the next event proves
[example: examples/prover/step-limits.lisp].

In a book, a step limit inside `must-fail` is how a deliberate failure
certifies quickly; most examples of this guide do it
[example: examples/prover/induction-lemma-first.lisp]. Rewrite loops usually
end sooner, at the rewriter's call-depth limit (chapter 2,
[:doc rewrite-stack-limit]).

## 1.11 `skip-proofs`, `defaxiom` and trust tags

### 1.11.1 `skip-proofs`

`(skip-proofs form)` processes the form "as usual except that the proof
obligations usually generated are merely assumed" [:doc skip-proofs]. The
manual's warning: "The use of `skip-proofs` carries an implicit promise by
the user that the ensuing proof obligations are indeed theorems of the
current theory. When that is not the case, `skip-proofs` can even allow
inconsistent events to be admitted to the logic" [:doc skip-proofs]. A
skipped `defun` is worse than a skipped `defthm`, "since not only is the
definitional equation being assumed but so are formulas relating to
termination and type"; "A proof script involving `skip-proofs` should be
regarded as work-in-progress, not as a completed proof with some unproved
assumptions" [:doc skip-proofs].

Certification refuses it by default: `:skip-proofs-okp` defaults to `nil`,
and "The value `nil` causes an error if such an event is found"
[:doc certify-book]. A book certified with `:skip-proofs-okp t` prints a
warning when certified and when included, and including it is an error if
`include-book` is given `:skip-proofs-okp nil` [:doc skip-proofs].

### 1.11.2 `defaxiom`: never

"WARNING: We strongly recommend that you not add axioms. If at all possible
you should use `defun` or `mutual-recursion` to define new concepts
recursively or use `encapsulate` to constrain them constructively ... Note
that adding new axioms may frequently render the logic inconsistent!"
[:doc defaxiom]. No `defaxiom` may appear inside an `encapsulate`
[:doc encapsulate], certification refuses one unless `:defaxioms-okp t`
[:doc certify-book], and no function that "syntactically supports a
`defaxiom` formula is allowed to get an attachment" [:doc defattach]. The
examples of this guide that the manual writes with `defaxiom` (free
variables, forward chaining, backchain limits) are rewritten with
`encapsulate` and a local witness, which proves the constraints consistent
[example: examples/rewriting/free-variables.lisp],
[example: examples/rewriting/forward-chaining.lisp].

fn's way to state an assumption without an axiom is an `encapsulate` with a
local witness per named assumption, `books/assumptions.lisp`, discharged for
a platform by functional instantiation: "every theorem that took
A-DURABILITY as a hypothesis transfers to that platform by
`(:functional-instance <theorem> (fn-assume-durability-image
qual-apfs-image))`, and the transfer is checked by ACL2 rather than asserted
in prose" [fn: docs/proofs.md:813 @3bbfc4dca]. fn's document also says the
encapsulates "state the assumptions; they do not yet apply them. No theorem
in the tree takes one as a hypothesis today"
[fn: docs/proofs.md:834 @3bbfc4dca].

### 1.11.3 Trust tags

Some facilities can introduce unsoundness and need an active trust tag, among
them `sys-call` and `progn!` [:doc defttag], and trusted clause processors
[:doc define-trusted-clause-processor]; "A trust tag
thus represents a contract: The writer of such a book is guaranteeing that
the book extends ACL2 in a ``correct'' way" [:doc defttag]. `(defttag :tag)`
activates one and prints a `TTAG NOTE`; `certify-book` and `include-book`
take a `:ttags` argument, which for `certify-book` defaults to none allowed;
the certificate records every ttag used by the book and its includes, local
ones included [:doc defttag]. A certifier who wants to trust a collection
should "certify all the user-supplied books from scratch and check either
that no `:ttags` were supplied to `certify-book`, or else look for every
`TTAG NOTE` in the standard output" [:doc defttag].

fn's rule for all three: "Do not turn `skip-proofs`, trust tags, or axioms
into a certification shortcut", and "Termination admission, guard
verification, theorem proof, book certification, and platform tests are
different evidence. A certified book can still depend on trusted facilities;
disclose those explicitly" [fn: docs/proofs.md:85 @3bbfc4dca].

## 1.12 Example index for this chapter

| example | technique |
| --- | --- |
| `examples/prover/false-conjecture.lisp` | a false conjecture found from its checkpoint and by evaluation |
| `examples/prover/induction-accumulator.lisp` | generalizing an accumulator theorem |
| `examples/prover/induction-lemma-first.lisp` | the missing lemma that makes induction unnecessary |
| `examples/prover/waterfall-rv-rv.lisp` | every waterfall process in one proof |
| `examples/prover/use-instance.lisp` | `:use` with `:instance`; the enabled-rule pitfall |
| `examples/prover/rule-classes-nil-use.lisp` | a `:rule-classes nil` lemma used by `:use` |
| `examples/prover/cases-hint.lisp` | `:cases` |
| `examples/prover/expand-hint.lisp` | `:expand` |
| `examples/prover/induct-hint.lisp` | `:induct`, and the lemma that replaces it |
| `examples/prover/subgoal-theory.lisp` | a `Goal` `:in-theory` lost at a subgoal |
| `examples/prover/by-and-restrict.lisp` | `:by`, `:restrict` |
| `examples/prover/nonlinearp.lisp` | `:nonlinearp` |
| `examples/prover/computed-hints.lisp` | computed hints, `set-default-hints` |
| `examples/prover/clause-processor.lisp` | a verified clause processor |
| `examples/prover/mutual-recursion-flag.lisp` | induction over a clique with `tools/flag` |
| `examples/prover/step-limits.lisp` | `:do-not-induct`, step limits, and what an abort means |
