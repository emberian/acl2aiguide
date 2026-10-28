# 2. Rewriting discipline, theories, books

Chapter 1 described the prover. This chapter is about what it proves with:
the rules in the database, the theories that decide which rules are
switched on, and the books that carry rules from one development to the
next. Most of an ACL2 user's work is here. The manual says so plainly about
the simplifier: "Good users spend most of their time thinking about how to
control the simplifier" [:doc architecture-of-the-prover].

Every technique has a certified book under `examples/rewriting/` or
`examples/books/`, certified with `examples/certify.sh` on the laptop ACL2
(8.7 on SBCL 2.6.8). Prover output was produced at the laptop REPL
(`~/tools/acl2-fn/acl2-literal-4g-tls64k`) from the forms of the cited
example, and the `[measured: ...]` tag names the form. fn, the
ACL2-verified NNTP server, is the worked example throughout; its documents
are cited at `origin/dev` `3bbfc4dca`.

## 2.1 Pitfalls first

1. **Two rules rewrite into each other**, and the prover stops with a call
   depth error, or loops until you interrupt it (section 2.5).
2. **A free variable in a hypothesis is never bound**, so a rule you proved
   never fires (section 2.4).
3. **A rule's hypothesis is a non-recursive function that the goal has
   already opened**, so the hypothesis cannot be relieved (sections 2.3,
   2.6.1).
4. **A book exports its internals.** Every includer then pays for rules it
   did not ask for; fn measured that most of its whole-tree rewriting was
   exactly this (section 2.9.6).
5. **A `local` include is mistaken for an interface**, or a non-local
   include of a book that withdraws nothing turns a quick proof into a timeout
   (section 2.9.5).
6. **A vocabulary is enabled book-wide** to make one proof work and makes
   every other proof in the book slow (section 2.8.6).
7. **A change low in the include graph recertifies everything above it**
   (section 2.10.6).
8. **A `must-fail` is read as a counterexample.** It is only the prover's
   refusal (section 2.10.9).

## 2.2 How a rule is made

### 2.2.1 Rule classes, and the default

"When `defthm` is used to prove a named theorem, rules may be derived from
the proved formula and stored in the database. The user specifies which kinds
of rules are to be built" [:doc rule-classes]. With no `:rule-classes`, "it
is as though what was specified was to make one or more `:rewrite` rules";
`:rule-classes nil` makes none [:doc rule-classes]. The classes are
`:rewrite`, `:rewrite-quoted-constant`, `:built-in-clause`,
`:clause-processor`, `:compound-recognizer`, `:congruence`, `:definition`,
`:elim`, `:equivalence`, `:forward-chaining`, `:generalize`, `:induction`,
`:linear`, `:meta`, `:refinement`, `:tau-system`, `:type-prescription`,
`:type-set-inverter` and `:well-founded-relation` [:doc rule-classes].

The manual's guidance on choosing: "at present we recommend that new ACL2
users rely almost exclusively on (conditional) rewrite rules. A reasonable
but slightly bolder approach is to use `:type-prescription` and
`:forward-chaining` rules for ``type-theoretic'' rules ... However, the rest
of the rule classes are really not intended for widespread use, but rather
are mainly for experts" [:doc rule-classes].

A rule class object may carry a `:corollary`: "the formula actually used to
justify the rule created and thus determines the form of the rule"; it must
follow from the theorem, and the prover is called to check that when it does
not follow trivially [:doc rule-classes]. This lets a theorem be stated in the
form a reader wants and stored in the form the prover needs.

Each rule gets a rune, `(:class name . x)`, where `x` numbers the rule
classes of one event when there is more than one [:doc rune]. One corollary
can produce several rules that share a rune, for a conjunction
[:doc rune].

`defthmd` proves a theorem and disables it in one event; it is for "users
who prefer working in a mode where theorems are only enabled when explicitly
directed by `:in-theory`" [:doc defthmd].

### 2.2.2 From formula to rewrite rule

ACL2 translates the corollary, expands macros, removes guard holders,
flattens nested `and` and `implies`, and expands `let`s, until each conjunct
is `(implies (and h1 ... hn) concl)`; it then coerces each conclusion to
`(equiv lhs rhs)` for a known equivalence relation, and "If we do not reach
an equivalence relation ... then we replace the resulting term, `term` by
`(iff term t)`, except that we replace `(not term)` by `(iff term nil)`"
[:doc rewrite]. So a predicate conclusion becomes a rule that rewrites the
predicate to true, valid only where propositional equivalence is enough,
which is reason (3c) in the tutorial's list of why a rule did not fire
[:doc introduction-to-key-checkpoints].

The left-hand side may not be a variable, a quoted constant, a `let` or a
`lambda` application, and a rule whose two sides are the same term is an
error, "since this rule will loop"; but "the rule could loop in other cases,
for example if `rhs` is an instance of `lhs`" [:doc rewrite].

`:pr` shows how a rule was stored. For `f1-is-f2` of
`examples/rewriting/loop-pair.lisp`:

```
Rune:         (:REWRITE F1-IS-F2)
Enabled:      T
Hyps:         (CONSP X)
Equiv:        EQUAL
Lhs:          (F1 X)
Rhs:          (F2 X)
Backchain-limit-lst: NIL
Subclass:     BACKCHAIN
Loop-stopper: NIL
```

[measured: `:pr f1-is-f2` after the events of examples/rewriting/loop-pair.lisp
up to `f2-is-f1`, laptop REPL, ACL2 8.7 / SBCL 2.6.8].

ACL2 warns at storage time about rules that are unlikely to fire. Two
warnings to read rather than skip:

```
ACL2 Warning [Non-rec] in ( DEFTHM F1-IS-F2 ...):  A :REWRITE rule
generated from F1-IS-F2 will be triggered only by terms containing
the function symbol F1, which has a non-recursive definition.  Unless
this definition is disabled, this rule is unlikely ever to be used.
ACL2 Warning [Subsume] in ( DEFTHM F1-IS-F2 ...):  The previously added
rule F1 subsumes a newly proposed :REWRITE rule generated from F1-IS-F2,
in the sense that the old rule rewrites a more general target.  Because
the new rule will be tried first, it may nonetheless find application.
```

[measured: `(defthm f1-is-f2 ...)` of examples/rewriting/loop-pair.lisp,
before `f1` is disabled, laptop REPL, ACL2 8.7 / SBCL 2.6.8]. The first says
the left-hand side's function will usually be opened before the rule is
tried; the second says, among other things, that newer rules are tried first.

## 2.3 How a rewrite rule is used

### 2.3.1 Match, relieve, replace

"A `:rewrite` rule is used when any instance of the `lhs` occurs in a
context in which the equivalence relation is an admissible congruence
relation. First, we find a substitution that makes `lhs` equal to the target
term. Then we attempt to relieve the instantiated hypotheses of the rule.
Hypotheses that are fully instantiated are relieved by recursive rewriting.
Hypotheses that contain ``free variables'' ... are relieved by attempting to
guess a suitable instance so as to make the hypothesis equal to some known
assumption in the context of the target. If the hypotheses are relieved, and
certain restrictions that prevent some forms of infinite regress are met
..., the target is replaced by the instantiated `rhs`, which is then
recursively rewritten" [:doc rewrite]. The rewriter "walks through a term
(typically left-to-right, innermost first) maintaining a list of known
assumptions"; for each target it retrieves "all the rules stored under the
topmost function symbol of the target and tries each rule in turn"
[:doc monitor].

Three refinements from the same topic: rewrite rules "are never applied to
quoted constants or any term inside a call of `hide`"; matching is generous
with constants, so a left-hand side `(f (+ 3 x))` matches `(f 10)` with `x`
bound to 7; and the rewriter looks up the already-rewritten values of bound
variables when it rewrites hypotheses and right-hand side, instead of
rewriting them again (see `double-rewrite` for when that matters)
[:doc rewrite].

### 2.3.2 Backchaining and its limits

Relieving a hypothesis by rewriting it is backchaining; each hypothesis of a
`:rewrite`, `:meta`, `:linear` or `:type-prescription` rule has a backchain
limit, `nil` (none) by default, settable per rule with
`:backchain-limit-lst` and globally with `set-backchain-limit`
[:doc backchain-limit]. "the relieving of hypotheses may be limited to the use
of contextual information (without backchaining, i.e., without recursively
rewriting hypotheses) by executing `:set-backchain-limit 0`"
[:doc backchain-limit]. The rule-classes topic adds that "you can set the
`:backchain-limit-lst` to 0 to avoid any attempt to relieve `force`d
hypotheses, which can lead to a significant speed-up in some cases"
[:doc rule-classes].

**Pitfall: non-recursive functions in hypotheses.** A hypothesis like
`(my-statep s)` where `my-statep` is enabled and non-recursive will often
fail to be relieved, because the goal's own `(my-statep s)` has already been
opened into its body. The manual explains this for `:type-prescription`
rules: "Since the hypothesis in the conjecture is rewritten, it will become
the conjunction of `(true-listp s)` and `(equal (len s) 2)` ... But type
reasoning will be unable to deduce that `(my-statep s)` has type `t` in this
context ... The moral is: beware of non-recursive functions occurring in the
hypotheses of `:type-prescription` rules" [:doc type-prescription]. The
remedy it gives is to disable the predicate or to write its body in the
hypothesis [:doc type-prescription]. (A small reconstruction of that example
in this guide's REPL did prove, so the manual's statement is quoted here as
its claim, not as a reproduced failure [measured: `my-statep` with a
constrained `sget` and a `:type-prescription` rule, laptop REPL, ACL2 8.7 /
SBCL 2.6.8].) The free-variables topic says the same for rewrite rules: a
hypothesis whose function "is nonrecursive and enabled" may never match
[:doc free-variables].

### 2.3.3 `force` and `case-split`

"`Force` is the identity function", but in a rule's hypothesis "the needed
instance of the hypothesis, `hyp'`, may be assumed if the usual process fails
to prove it or its negation. In that situation, if the rule is eventually
applied, then a special case is generated, requiring the system to prove that
`hyp'` is true in the current context. The proofs of all such ``forced
assumptions'' are, by default, delayed until the successful completion of the
main goal" [:doc force]. "Since a forced hypothesis must be provable whenever
the rule is otherwise applicable, forcing should be used only on hypotheses
that are expected always to be true", typically guards and the hypotheses of
"most general" type-prescription lemmas [:doc force].

`examples/rewriting/force.lisp` shows both outcomes. Where the context does
establish the forced hypothesis, the proof goes through. Where nothing says
the argument is a state, the rule fires anyway, the prover prints "q.e.d.
(given one forced hypothesis)", and "Forcing Round 1" then fails on that
hypothesis, failing the proof [example: examples/rewriting/force.lisp],
[measured: the final `thm` of examples/rewriting/force.lisp, laptop REPL,
ACL2 8.7 / SBCL 2.6.8]. A failed forcing round is a statement about the
context, not about the rule.

`case-split` is the variant that "does not delay the ``false case'' to a
forcing round but tackles it more or less immediately", producing a subgoal
in which the hypothesis is assumed false [:doc case-split]. Neither splits
while an `if` remains in the goal: "the rewriter is never willing to force
when there is an `if` term present in the goal being simplified"
[:doc force], [:doc case-split]. Disabling `(:executable-counterpart force)`
turns forcing off [:doc force].

### 2.3.4 `syntaxp` and `bind-free`

`syntaxp` "always returns `t` and so may be added as a vacuous hypothesis.
However, when relieving the hypothesis, the test ``inside'' the `syntaxp` form
is actually treated as a meta-level proposition about the proposed
instantiation of the rule's variables" [:doc syntaxp]. The test sees each
variable bound to the *quoted term* it matched, not its value: "we are asking
``Is the list `(trn a b)` a `consp` and if so, is its `car` the symbol
`NORM`?''" [:doc syntaxp]. It deals "with the syntactic form used internally
by ACL2, rather than that seen by the user"; `:trans` shows that form
[:doc syntaxp].

The standard use is stopping a rule that would otherwise rewrite its own
output. `(equal (lxd x) (lxd (nrm x)))` loops,
`(lxd a) -> (lxd (nrm a)) -> (lxd (nrm (nrm a))) -> ...`; the guarded rule

```lisp
(defthm lxd-normalize
  (implies (syntaxp (not (and (consp x) (eq (car x) 'nrm))))
           (equal (lxd x) (lxd (nrm x)))))
```

fires once and stops [:doc syntaxp], [example: examples/rewriting/syntaxp.lisp].

`bind-free` is "like `syntaxp`, in that it logically always returns `t` but
may affect the application of a ... rule when it is called at the top-level
of a hypothesis. It is like a `:meta` rule, in that it allows the user to
perform transformations of terms under programmatic control"
[:doc bind-free]. Its term returns an alist binding free variables to terms
(or a list of such alists, tried in turn), or `nil` for failure; the optional
second argument lists the variables it may bind, and the manual "strongly
recommend[s]" giving it [:doc bind-free]. Section 2.4 uses it.

fn found that neither `syntaxp` nor `bind-free` tests count as prover steps
or appear as frames, so a book slowed by a library's tests shows `prove` time
large and steps few, invisible to step-based profiling
[fn: docs/proof-style.md:621 @3bbfc4dca].

## 2.4 Free variables

**Pitfall.** A variable is free in hypothesis `hi` "if [it does] not occur
in `lhs` or in any `hj` with `j<i`" [:doc free-variables]. ACL2 warns when it
stores such a rule:

```
ACL2 Warning [Free] in ( DEFTHM REL-TRANS ...):  A :REWRITE rule generated
from REL-TRANS contains the free variable Y.  This variable will be
chosen by searching for an instance of (REL X Y) in the context of
the term being rewritten.  This is generally a severe restriction on
the applicability of a :REWRITE rule.  See :DOC free-variables.
```

[measured: `(defthm rel-trans (implies (and (rel x y) (rel y z)) (rel x z)))`
inside an `encapsulate` constraining `rel`, laptop REPL, ACL2 8.7 / SBCL
2.6.8].

### 2.4.1 The three ways a free variable is bound

The rewriter relieves a hypothesis with free variables by these steps, in
order [:doc free-variables]:

1. A *binding hypothesis* `(equal var term)` (or `(equiv var (double-rewrite
   term))`), with `var` free and `term` fully bound, binds `var` to the
   rewritten `term`.
2. Otherwise it looks "for a binding of the free variables of the
   hypothesis so that the corresponding instance of the hypothesis is known
   to be true in the current context".
3. Otherwise it searches "all enabled, hypothesis-free rewrite rules of the
   form `(equiv lhs rhs)`, where `lhs` has no variables", for a ground fact
   matching the hypothesis.

Steps 1 and 3 are skipped for forward-chaining rules, and step 3 for
type-prescription rules [:doc free-variables].

### 2.4.2 `:match-free :once` and `:all`

When the first binding found leads to a later hypothesis failing, `:all`
backtracks to other bindings and `:once` does not [:doc free-variables].
`:all` is "generally the better choice because of its greater power,
provided the user does not introduce a large number of rules with free
variables, which has been known to slow down the prover due to combinatorial
explosion in the search" [:doc free-variables]. The default without a
`:match-free` field is `:all`, with a warning, unless `set-match-free-default`
says otherwise; `set-match-free-default` is local to a book, and
`add-match-free-override` changes existing rules [:doc set-match-free-default],
[:doc free-variables].

`examples/rewriting/free-variables.lisp` certifies the manual's transitivity
example with an `encapsulate` in place of its `defaxiom`. Rewriting
`(rel a d)` binds `x` to `a` and `z` to `d`; the context lists `(rel a b)`
before `(rel a c)`; `:once` binds `y` to `b`, `(rel b d)` is unknown, and the
proof fails; `:all` backtracks to `y = c` and succeeds
[example: examples/rewriting/free-variables.lisp].

Hypothesis order matters: "it is good practice to put the ``more
substantial'' hypotheses first, so that the most likely bindings of free
variables will be found first (in the case of `:all`) or found at all (in the
case of `:once`)" [:doc free-variables]. A cheap type hypothesis first, like
`(rationalp y)`, binds `y` to the first rational in sight and wastes the
search on it [:doc free-variables].

### 2.4.3 When no search can bind it: `bind-free`, `:restrict`, forward chaining

If the fact that would bind the variable is a rule with variables on its left
side rather than a fact in the context, none of the three steps finds it. In
`examples/rewriting/bind-free.lisp`, `(implies (lo x y) (hi x))` cannot prove
`(hi a)` although `(lo v (cons v 4))` is a theorem; a `bind-free` hypothesis
that proposes the candidates `(cons x 3)` and `(cons x 4)` for `y` makes the
rule fire, the second candidate succeeding [example:
examples/rewriting/bind-free.lisp], [:doc bind-free]:

```lisp
(defthm lo-implies-hi-with-candidates
  (implies (and (bind-free (lo-candidates x) (y))
                (lo x y))
           (hi x)))
```

Two other remedies. A `:restrict` hint fixes the binding for one proof
(chapter 1, [example: examples/prover/by-and-restrict.lisp]). And a
`:forward-chaining` rule can put the binding fact into the context where
step 2 finds it; the manual's forward-chaining topic says "forward chaining
may be indispensable in a scenario with free-variables, whose handling is
quite weak with rewrite rules" [:doc forward-chaining], and
`examples/rewriting/forward-chaining.lisp` certifies its example: the same
implication fails as a rewrite rule and works as a forward-chaining rule
[example: examples/rewriting/forward-chaining.lisp].

## 2.5 Loops

### 2.5.1 How a loop looks

ACL2 limits the depth of certain rewriter calls "using the value of the form
`(rewrite-stack-limit (w state))`", because rewrite rules "have the potential
of causing an infinite loop in the ACL2 rewriter. This could lead to Lisp
stack overflows and even segmentation faults" [:doc rewrite-stack-limit].
When the limit is hit the error names the tools:

```
HARD ACL2 ERROR [Call depth] in REWRITE:  The call depth limit of 1000
has been exceeded in the ACL2 rewriter.  To see why the limit was exceeded,
first execute
  :brr t
and then try the proof again, and then execute the form (cw-gstack)
or, for less verbose output, instead try (cw-gstack :frames 30).  You
may then notice a loop caused by some set of enabled rules, some of
which you can then disable; see :DOC disable.  For a possible solution
when there is not a loop, see :DOC rewrite-stack-limit.
```

[measured: the looping `thm` of examples/rewriting/loop-pair.lisp, laptop
REPL, ACL2 8.7 / SBCL 2.6.8]. When the looping rules are "simple"
abbreviations, the loop happens in preprocessing and the message says
`in PREPROCESS` and suggests retrying with `:do-not '(preprocess)`
[measured: the looping `thm` of examples/rewriting/syntaxp.lisp, laptop REPL,
ACL2 8.7 / SBCL 2.6.8]. A loop that does not deepen the stack, or a case
explosion, shows instead as a prover that "goes silent for a very long time",
which the tutorial attributes to "some kind of rewrite loop caused by rules
that cause it to flip back and forth between various supposedly normal forms,
or else ... a huge number of cases" [:doc introduction-to-key-checkpoints].

The frames show the loop. With `:brr t`, after the failure,
`(cw-gstack :frames '(5 12))` prints

```
5. Attempting to apply (:REWRITE F1-IS-F2) to
     (F1 A)
6. Rewriting (to simplify) the rhs of the conclusion,
     (F2 X),
   under the substitution
     X : A
7. Attempting to apply (:REWRITE F2-IS-F1) to
     (F2 A)
8. Rewriting (to simplify) the rhs of the conclusion,
     (F1 X),
   under the substitution
     X : A
9. Attempting to apply (:REWRITE F1-IS-F2) to
     (F1 A)
...
```

[measured: `:brr t`, the looping `thm`, `(cw-gstack :frames '(5 12))`, events of
examples/rewriting/loop-pair.lisp, laptop REPL, ACL2 8.7 / SBCL 2.6.8]. A loop
caught by an interrupt rather than the depth limit is read the same way
[:doc cw-gstack]. `accumulated-persistence` finds rules that are tried often
to no purpose, which is how a slow loop or near-loop looks in aggregate
[:doc accumulated-persistence].

### 2.5.2 The pair of rules that rewrite each other

`examples/rewriting/loop-pair.lisp` has two true rules, `(f1 x) = (f2 x)` and
`(f2 x) = (f1 x)` under `(consp x)`, both enabled: the loop above. The repair
is to choose a normal form and keep one direction, then record the choice
[example: examples/rewriting/loop-pair.lisp]:

```lisp
(theory-invariant (incompatible (:rewrite f1-is-f2) (:rewrite f2-is-f1))
                  :key f1-f2-direction)
```

after which any theory that enables both is an error (the book checks that
with `must-fail`) [example: examples/rewriting/loop-pair.lisp]. The community
practice is the same: "Sets of rules which are known to cause rewrite loops
should be declared incompatible as a theory-invariant" [:doc best-practices].

fn's instance is less visible. In `books/store-log.lisp`, `fn-lg-slice` is
defined as `(let ((n (fn-lg-declared-len octets))) (if (and n (<= n (len
octets))) (fn-bs-take n octets) nil))`
[fn: books/store-log.lisp:368 @3bbfc4dca], and `books/store-log-stream.lisp` proves
`fn-lgw-slice-is-take`, which rewrites `(fn-bs-take (fn-lg-declared-len x) x)`
to `(fn-lg-slice x)` [fn: books/store-log-stream.lisp:335 @3bbfc4dca].
In the branch where its test holds, opening `fn-lg-slice` produces exactly
the left side of that rule whenever `fn-lg-declared-len` stays closed, and the
rule's hypotheses are that same test. fn's rule-hygiene lane found this while
withdrawing rules the profile called useless: its probe failed with
`(:DEFINITION FN-LG-SLICE)` and `(:REWRITE FN-LGW-SLICE-IS-TAKE)` at the head
of the rules it counted [cv: a97d40c2#529], and fn's style document records
the lesson: "A rule can also be never-useful by the profile yet load-bearing:
its being enabled keeps a pair of rules from looping (the definition of
`fn-lg-declared-len` keeps `fn-lgw-slice-is-take` and `fn-lg-slice`'s
definition from rewriting each other ...)"
[fn: docs/proof-style.md:549 @3bbfc4dca]. That is a theory invariant written in prose. The mechanical form
is `(theory-invariant (incompatible ...))` over the two directions, or
stating the loop's two halves so that one of them is never a rewrite rule.

### 2.5.3 Loop-stoppers

A permutative rule such as commutativity would loop on its own output, and
ACL2 prevents that: `commutativity-of-+` "creates a rewrite rule with a
loop-stopper of `((x y binary-+))`. This means, very roughly, that the term
corresponding to `y` must be ``smaller'' than the term corresponding to `x` in
order for this rule to apply" [:doc loop-stopper]. The order is a total
order on terms, adjusted so that "invisible" unary functions such as
`unary--` inside `+` are ignored; the effect is that a set of permutative
rules sorts the arguments of a tree of calls [:doc loop-stopper]. ACL2
computes the field when "`rhs` is ... an instance of the left hand side by a
substitution whose range is a list of distinct variables"
[:doc loop-stopper].

`examples/rewriting/loop-stopper.lisp` shows the stored
`Loop-stopper ((X Y OP))` doing its job, and the same rule declared with
`:loop-stopper nil` looping on `(op b a)` [example:
examples/rewriting/loop-stopper.lisp]. A rule that rewrites to a
*non-permutative* instance of its own left side, like `lxd-normalize` above,
gets no loop-stopper; `syntaxp` is the tool there (section 2.3.4).

## 2.6 The other rule classes

### 2.6.1 `:type-prescription`

A type-prescription rule says that a term has a type, under hypotheses:
"when asked to determine the type of a term that is an instance of `pat`,
ACL2 will first attempt to establish the hypotheses. **This is done by type
reasoning alone, not rewriting!**", except that a forced hypothesis may reach
the rewriter [:doc type-prescription]. `defun` makes one for each function
when it can, as `(:type-prescription fn)` [:doc type-prescription]. Type
reasoning is "a relatively basic rule-based theorem prover for questions
about Common Lisp types", run over a context of assumptions called a
type-alist [:doc type-reasoning]. Because only type reasoning relieves the
hypotheses, the non-recursive-hypothesis pitfall of section 2.3.2 is sharpest
here [:doc type-prescription].

### 2.6.2 `:forward-chaining`

"Forward chaining is performed as part of the simplification process: before
the goal is rewritten a *context* is established ... Forward chaining is used
to extend the context before rewriting begins" [:doc forward-chaining]. To
relieve its hypotheses ACL2 uses "only ... type reasoning, evaluation of
ground terms, and presence among our known assumptions. We do not use
rewriting" [:doc forward-chaining]. The conclusion goes into the context,
not the goal, so "you will not see it in the goal formula", and it is added
"with no simplification or rewriting applied" [:doc forward-chaining]. The
trigger defaults to the atom of the first hypothesis; `:trigger-terms` names
others [:doc forward-chaining]. When to choose it: "if a conclusion like
`(p1 A)` is expected to be widely needed, it is better to derive it via
forward chaining ... Thus forward chaining is pro-active and backward
chaining (rewriting) is reactive" [:doc forward-chaining].

fn uses forward chaining for exactly the facts it does not want as rewrite
rules. Its record generator withdraws the definitions of a record's shape
predicate and accessors, which takes away facts type reasoning used to get by
opening them, `(consp a)` from `(stringp (fn-article-msgid a))` for instance;
so the generator "emits, beside the record lemmas and as `:forward-chaining`
rules only (never rewrite), the three shape facts type reasoning used to
supply" [fn: docs/proof-style.md:153 @3bbfc4dca]. "Forward-chaining is the
right class: the facts land in the context when the record is mentioned, and
no rewrite rule about `consp` or `true-listp` leaves the book"
[fn: docs/proof-style.md:177 @3bbfc4dca]. The accessor fact triggers on the
field term itself, with `:trigger-terms ((fn-article-msgid x))`
[fn: docs/proof-style.md:166 @3bbfc4dca].

### 2.6.3 `:linear`

`:linear` rules feed the linear arithmetic procedure. The conclusion is an
inequality (or equality); the rule is stored under trigger terms, by default
"the list of all ``maximal addends'' in the concluding inequality"; and when
the procedure has a pot labelled with an instance of a trigger, it relieves
the hypotheses "with general-purpose rewriting" and adds the instantiated
inequality [:doc linear]. "It is generally best to specify as a trigger term
one of the ``maximal'' terms of the polynomial", or the new inequality lands
in another pot and does not cancel [:doc linear].
`examples/rewriting/linear.lisp` proves `(<= (cnt (firsts x)) (cnt x))` once,
`:rule-classes nil`, shows linear arithmetic unable to finish a bound with
`cnt` and `firsts` closed, and finishes it with the same fact as a `:linear`
rule [example: examples/rewriting/linear.lisp].

fn's note from its shared-books lane: "A `:linear` rule with
`:trigger-terms` and a `:rewrite` class on the same conclusion crashed SBCL
with a memory fault ... Split it into a type rule and a plain `:linear` rule"
[fn: docs/proof-style.md:911 @3bbfc4dca].

### 2.6.4 `:definition`

A `:definition` rule is an alternative definition proved as a theorem: "These
rules are not true ``definitions'' in the sense that they (a) cannot introduce
new function symbols and (b) do not have to be terminating recursion schemes.
They are just conditional rewrite rules that are controlled the same way we
control recursive definitions" [:doc definition]. The rewritten body must
pass the expansion heuristics, recursive calls with arguments already in the
goal or simpler controlling arguments [:doc definition]. The
`:install-body` field decides whether the rule becomes the body used by later
`:expand` hints [:doc rule-classes]. `examples/rewriting/definition-rule.lisp`
opens a length function two elements at a time with the original definition
disabled [example: examples/rewriting/definition-rule.lisp].

### 2.6.5 `:elim`

"an `:elim` rule ... has the effect of generalizing so-called ``destructor''
function applications to variables", the built-in example being
`car-cdr-elim`, `(implies (consp x) (equal (cons (car x) (cdr x)) x))`
[:doc elim]. Chapter 1's waterfall transcript shows it applied
[example: examples/prover/waterfall-rv-rv.lisp].

### 2.6.6 `:equivalence`, `:congruence`, `:refinement`

A Boolean two-place function proved reflexive, symmetric and transitive is an
equivalence relation; `(defequiv equiv)` generates the theorem
[:doc equivalence]. Rewrite rules whose conclusion is `(equiv lhs rhs)` are
then used only where `equiv` may be maintained, which congruence rules
establish: `(implies (equiv1 xk xk-equiv) (equiv2 (fn ... xk ...) (fn ...
xk-equiv ...)))` records "that the `equiv2`-equivalence of `fn`-expressions
can be maintained if, while rewriting the `k`th argument position,
`equiv1`-equivalence is maintained"; `defcong` writes it [:doc congruence].
A refinement rule records that one equivalence implies another, so the finer
relation's rules can be used where the coarser is maintained
[:doc refinement].

`examples/rewriting/congruence.lisp` defines `lequiv` (equal after a list
fix), proves `(lequiv (lfix x) x)` as a rewrite rule, and shows it unusable
under `cnt` until `(defcong lequiv equal (cnt x) 1)` is proved; then
`(cnt (lfix (lfix x)))` rewrites to `(cnt x)` with no induction
[example: examples/rewriting/congruence.lisp]. fn's style document weighs
`fty::defprod` against its raw-list records and concludes that what remains
"genuinely `fty`-only is congruence reasoning over record equivalences"
[fn: docs/proof-style.md:732 @3bbfc4dca].

### 2.6.7 `:meta` and `:clause-processor`

"Meta rules extend the ACL2 simplifier with hand-written code to transform
certain terms to equivalent ones", justified by a theorem over an evaluator
that the metafunction preserves meaning, and triggered on the function
symbols listed in `:trigger-fns` [:doc meta]. A clause processor works on
whole goals and is applied only by hints [:doc clause-processor]; chapter 1
certifies one [example: examples/prover/clause-processor.lisp].

### 2.6.8 `:induction`

"The definitional principle automatically creates an `:induction` rule, named
`(:induction fn)`, for each admitted recursive function, `fn`. It is this rule
that links applications of `fn` to the induction scheme it suggests.
Disabling `(:induction fn)` will prevent `fn` from suggesting the induction
scheme" [:doc induction]. A user `:induction` rule links a `:pattern` to the
scheme of a `:scheme` term, under a `:condition` checked by type reasoning;
"no theorem need be proved", so the recommended form has `t` as the theorem
[:doc induction]. `examples/rewriting/induction-rule.lisp` disables
`(:induction drop)`, shows `drop-of-drop` failing, and restores it with a rule
that sends `(drop n x)` to the scheme of `(tk n x)` [example:
examples/rewriting/induction-rule.lisp]:

```lisp
(defthm drop-suggests-tk-induction
  t
  :rule-classes ((:induction :pattern (drop n x)
                             :scheme (tk n x))))
```

### 2.6.9 `:compound-recognizer`

A compound-recognizer rule tells type reasoning which primitive types a
recognizer implies, as the built-in `natp-compound-recognizer` does for
`natp` [:doc compound-recognizer]. `examples/rewriting/compound-recognizer.lisp`
shows a hypothesis `(integerp x)` that cannot be relieved from `(smallp x)`
until such a rule exists, *with the tau system off*. With tau on (the
default) the same goal proves with no rule about `smallp`, and so does the
manual's own example with `natp-compound-recognizer` disabled
[example: examples/rewriting/compound-recognizer.lisp], [measured: the
`triple` example of :doc compound-recognizer with
`(disable natp-compound-recognizer)` and with
`(disable natp-compound-recognizer (tau-system))`, laptop REPL, ACL2 8.7 /
SBCL 2.6.8]. The two systems overlap; section 2.8.8 is about tau.

### 2.6.10 `:tau-system`

"every `defun` and every `:corollary` ... of every `defthm` stored as a rule
*of any* `:rule-class` is inspected to determine if it is of one of the forms
below", in the default greedy mode, and added to the tau database; `:rule-classes
:tau-system` adds a tau rule and nothing else, and `:rule-classes nil`
keeps a theorem out [:doc tau-system]. The forms are Boolean, Eval, Simple,
Conjunctive, signature, bounder, big-switch and mv-nth-synonym rules about
monadic predicates [:doc tau-system].

### 2.6.11 `:rule-classes nil`

`:rule-classes nil` stores the theorem and no rule [:doc rule-classes], so it
changes no later proof until cited by `:use` or `:by`
[example: examples/prover/rule-classes-nil-use.lisp]. fn requires it for
guard-proof equalities, for facts that restate one branch of a definition
(named `-is-no-op` and the like, with a `-by-definition` comment), and for
corollaries whose proof is `:in-theory '(A B)`
[fn: docs/proof-style.md:242 @3bbfc4dca], [fn: docs/proof-style.md:510 @3bbfc4dca]. Its record generator
makes constructor injectivity `:rule-classes nil` too, "a name for one
includer's `:use` rather than a rewrite rule that fires on every constructor
equality" [fn: docs/proof-style.md:137 @3bbfc4dca].

## 2.7 Normal forms

A rewrite rule chooses a normal form: every term matching its left side
becomes its right side. A set of rules is coherent when the normal forms
agree; the loop of section 2.5.2 is two rules that disagree. The tutorial's
list of reasons a known rule did not fire is mostly about normal forms: the
left side does not match the target, or the target is not where the rule's
equivalence applies [:doc introduction-to-key-checkpoints].

The community books agree on some forms for compatibility:
"Write lemmas in terms of `(mv-nth n ...)` instead of `(caddr ...)`", with
`mv-nth` disabled, because "Leaving `mv-nth` enabled is worse because it leads
to different normal forms for slot 0 versus other slots"
[:doc conventional-normal-forms]. Rule names follow the left side: "we base
the rule name on a reading of the left-hand side, using `of` as a separator",
`append-of-cons`, `true-listp-of-append`; `-when-hyp` for one simple
hypothesis; `-under-equiv` for rules about other equivalences
[books: doc/practices.lisp:511].

fn's records are the normal-form discipline applied to data. After a record's
constructor come "the shape lemma and one accessor-of-constructor lemma per
field; then the `:definition` runes of the shape, the accessors and the
constructor are withdrawn under the name `<record>-internals`. Nothing below
that point opens a record: rules are stated in accessor vocabulary and goals
stay in it" [fn: docs/proof-style.md:81 @3bbfc4dca]. The same document
forbids the rules that would pull goals out of that vocabulary from leaving a
book: "`len`-, `consp`- or `true-listp`-backchaining rules; `-is-`/`-of-`
equalities other than record lemmas"
[fn: docs/proof-style.md:529 @3bbfc4dca]. Opening the vocabulary book-wide breaks the normal form the
other way: in `books/checkpoint-codec.lisp` "it opened the parse result to
`car`/`cadr` so a domain lemma stated in accessor vocabulary stopped matching
the induction goals" [fn: docs/proof-style.md:747 @3bbfc4dca].

## 2.8 Theories

### 2.8.1 Runes and runic designators

"A theory is a list of ``runic designators'' ... Theories are used to control
which rules are ``enabled,'' i.e., available for automatic application by the
theorem prover. There is always a ``current'' theory" [:doc theories]. The
designators [:doc theories]:

- a rune, `(:rewrite foo)`;
- a function name `fn`, meaning `(:definition fn)` and `(:induction fn)`;
- `(fn)`, meaning `(:executable-counterpart fn)`;
- a theorem name, meaning all the rules it introduced;
- a `deftheory` name;
- the abbreviations `(:d fn)`, `(:e fn)`, `(:i fn)`, `(:r name)` and `(:t fn)`
  for definition, executable counterpart, induction, rewrite and
  type-prescription runes.

So "including a function name ... in the current theory enables that
function but does not enable the executable-counterpart" [:doc theories].
`defund` disables a definition and leaves the rest:
`(disabledp 'fact)` after `(defund fact ...)` is
`((:definition fact) (:induction fact))`
[example: examples/rewriting/theories.lisp].

### 2.8.2 `enable`, `disable`, `e/d`, `in-theory`

`(enable n1 ... nk)` is "the theory that contains all the names in the
current theory plus those listed"; `disable` removes; `(e/d (e...) (d...)
...)` is the sequence of enables and disables in order [:doc enable],
[:doc disable], [:doc e/d]. `(in-theory term)` makes a theory current; "it is
often useful to surround `in-theory` events with `local`" so the change is
not exported [:doc in-theory]. As a hint, `:in-theory` is evaluated against
the world, not the parent goal's theory (chapter 1, section 1.8.6,
[example: examples/prover/subgoal-theory.lisp]).

### 2.8.3 Named theories: `deftheory`, `current-theory`, `minimal-theory`, `ground-zero`

`(deftheory name term)` associates the runic theory of `term` with `name`;
"the theory being defined depends on the context", so a `deftheory` computed
from `(current-theory :here)` in a book can differ at include time from the
certification pass, which is what `deftheory-static` is for [:doc deftheory],
[:doc deftheory-static]. `(current-theory 'name)` is the theory current
just after `name` [:doc current-theory]. `minimal-theory` "enables only a few
built-in functions and executable-counterparts" and is meant for proofs that
follow from `:use`d lemmas [:doc minimal-theory]. `ground-zero` is the theory
at the end of boot-strapping, `(in-theory (current-theory 'ground-zero))`
restoring it [:doc ground-zero].

fn's uses. Named vocabularies: "Lemmas that are proof vocabulary ... are
withdrawn under a name, so a book above can re-enable exactly that vocabulary
in one line without knowing the list"
[fn: docs/proof-style.md:215 @3bbfc4dca]. `ground-zero` for lemmas about primitives: "A lemma about ACL2
primitives alone (`butlast`, `nthcdr`, `take`, `len`) is proved in
`(theory 'ground-zero)`: no book's rule can help it"
[fn: docs/proof-style.md:432 @3bbfc4dca]. `minimal-theory` as a smell: "A
hint that reaches for `minimal-theory` is a book that exported too much; say
which rules you mean with `e/d`" [fn: docs/proof-style.md:534 @3bbfc4dca].
`examples/rewriting/theories.lisp` certifies a named vocabulary enabled in
one hint and a lemma proved in `(theory 'ground-zero)`
[example: examples/rewriting/theories.lisp].

### 2.8.4 `theory-invariant`

`theory-invariant` adds a term "checked each time a theory expression is
evaluated"; `(incompatible r1 r2)` is the common invariant, and `:error nil`
makes a violation a warning [:doc theory-invariant]. The invariant must hold
when it is added [:doc theory-invariant]. "Theory invariants are particularly
useful in the context of large rule sets intended for re-use. Such sets often
contain conflicting rules, e.g., ... rules that rewrite in opposite
directions and thus loop if simultaneously enabled" [:doc theory-invariant].
A local redefinition of an invariant can make the second pass of an
`encapsulate` or a book's include pass fail, because the local event is
skipped there [:doc theory-invariant].

### 2.8.5 Executable counterparts

"If `(:executable-counterpart fn)` is enabled, then when applications of `fn`
to known constants are seen by the simplifier they are computed out by
executing the Common Lisp code for `fn`"; disabling it prevents that, which
can let lemmas about the subroutines apply instead [:doc
executable-counterpart]. `examples/rewriting/theories.lisp` proves
`(equal (fact 5) 120)` by evaluation and shows the same goal failing with
`(:e fact)` disabled, even with the definition enabled: the definition alone
is not opened five times [example: examples/rewriting/theories.lisp].
Constrained functions have executable counterparts that trap; a ground call
that reaches one becomes a `HIDE`d term, which is why the manual's
functional-instantiation example disables the executable counterpart of a
function that calls a constrained one [:doc executable-counterpart],
[:doc functional-instantiation-example].

### 2.8.6 Which rules a library should leave enabled

The community's recommendations for a "Widget library": "Avoid any non-local
inclusion of arithmetic libraries"; "Avoid any non-local `(in-theory ...)`
events that involve built-in ACL2 functions"; and respect the ACL2 namespace
[:doc theory-management]. From best-practices: "Top-level `include-book` and
`in-theory` events should be at the top of the book"; they "should be local
where possible"; and "Most functions (especially non-recursive function)
should be disabled by default, unless they are best understood as simple
aliases/wrappers" [:doc best-practices].

fn's rule for the includer: "An includer that needs another cluster's
withdrawn vocabulary enables it in the one `verify-guards` or `defthm` hint
that needs it, never with a book-level `(in-theory (enable ...))`. Measured
twice on 2026-09-20: a book-wide enable of the codec vocabularies made every
`:guard t` definition pay for the open codec (`books/config.lisp`, minutes per
form)" [fn: docs/proof-style.md:747 @3bbfc4dca]. And for recognizers: prove a
theorem about a transition "with the recognizer and every sub-recognizer
CLOSED"; a local enable of `fn-tcl-sessionp` above one theorem "put its eleven
sub-recognizers into the clause and produced 1082 subgoals; closed, the same
theorem took 0.30 s" [fn: docs/proof-style.md:760 @3bbfc4dca].

### 2.8.7 Non-linear arithmetic

`(set-non-linearp t)` turns on non-linear arithmetic for later events; it is
local to the book [:doc set-non-linearp]. Chapter 1 has the hint form
[example: examples/prover/nonlinearp.lisp].

### 2.8.8 The tau system

The tau system extends type reasoning with facts about monadic predicates; it
is switched by "the rune `(:EXECUTABLE-COUNTERPART TAU-SYSTEM)`", so
`(in-theory (disable (tau-system)))` turns it off [:doc tau-system]. fn found
it can be the time sink in a book, with `prove` large and steps few, and
measured it tree-wide with `tools/tau_cost.py`, which loads every book with
tau on and off: "Tau is not uniformly waste: of 1,445 books, tau off cost
1,400 s more than it saved in total ... Keep it on by default; turn it off in
a book where the confirmation measured the saving"
[fn: docs/proof-style.md:633 @3bbfc4dca]. Where it is turned off, fn keeps `(local (in-theory (disable
(tau-system))))` after the includes and enables it locally around the forms
that need it [fn: docs/proof-style.md:629 @3bbfc4dca].
`examples/rewriting/compound-recognizer.lisp` shows tau proving a goal that
type reasoning alone cannot, which is why turning it off is a measured
decision [example: examples/rewriting/compound-recognizer.lisp].

## 2.9 `local` and the export boundary

### 2.9.1 `local`

"`(local ev)` is equivalent to `ev`" in `:logic` mode during admission, and a
no-op when including: such events "are processed when the encapsulation or
book is checked for admissibility in `:logic` mode but are skipped when
extending the host world. Such events are thus considered ``local'' to the
verification of the encapsulation or book. The non-local events are the ones
``exported''" [:doc local]. "you can't make an event local if its presence is
required to make sense of a non-local one" [:doc local].

### 2.9.2 `encapsulate`, constrained functions and their witnesses

An `encapsulate` is processed in two passes. "On the first pass, each
sub-event is printed (by default) and processed in sequence ... Then a second
pass is made after rolling back the logical world ... In the second pass,
only the non-local forms `<event-i>` are evaluated, again in order, and
proofs are skipped" [:doc encapsulate]. With a non-empty signature list it
introduces constrained functions: "the local definitions of the constrained
functions are just ``witness functions'' that establish the consistency of
the constraints. Because those definitions are local, they are not present in
the theory produced by encapsulation", and theorems about the constrained
functions "necessarily employ only the constraints" [:doc encapsulate].

The two characteristic errors are local incompatibilities: "(1) a locally
defined function or macro was used in a non-local event ... and (2) the
witnessing definition of a function that was included among the signatures
of an `encapsulate` was not made local" [:doc local-incompatibility]. Also
forbidden: `defaxiom` anywhere inside, and non-local `include-book` inside an
`encapsulate` with signatures [:doc encapsulate]. Calls of a constrained
function "cannot be evaluated in the ACL2 read-eval-print loop" without an
attachment [:doc encapsulate].

### 2.9.3 Functional instantiation

A theorem about constrained functions can be instantiated to concrete ones:
`(:functional-instance lmi (f1 g1) ... (fn gn))` denotes the theorem with the
`fi` replaced by the `gi`, but "before such a lemma instance can be used, the
system will generate proof obligations arising from the replacement of the
`fi`'s by the `gi`'s in constraints that ``support'' the lemma"
[:doc lemma-instance]. Defined functions whose definitions mention a
constrained function take part as well; in the manual's example the
instantiation replaces `ac-fn-list` and `ac-fn-domain-list` alongside
`ac-fn`, `ac-fn-root` and `ac-fn-domain` [:doc
functional-instantiation-example].

`examples/books/encapsulate-fi.lisp` constrains a Boolean `ok`, proves
`all-ok-of-append` from the constraint alone, and obtains the corresponding
theorems for `integer-listp` and `symbol-listp`, each for one hint
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

fn uses this layering for its named assumptions (chapter 1, section 1.11.2)
and for loop twins and carried invariants, whose generic theorems are proved
once and instantiated per instance (`def-carried` "emits the trace theorem
`NAME-run-carries` by functional instantiation of a generic theory")
[fn: docs/proof-style.md:306 @3bbfc4dca].

### 2.9.4 `defattach`

`(defattach f g)` makes calls of constrained `f` evaluate through `g`;
logically, evaluation takes place in a theory extended with the "attachment
equation" `(equal (f x) (g x))`, which ACL2 guarantees consistent; the proof
obligation is that `g` satisfies `f`'s constraints and that `f`'s guard
implies `g`'s [:doc defattach]. Attachments are not used for "evaluation of
ground terms (terms without free variables) during proofs" [:doc defattach].
`examples/books/defattach-exec.lisp` shows a constrained order that cannot be
evaluated, attaches `greater-rationalp`, evaluates the generic `best` on
`'(3 1 2)` to `3`, and shows that a proof still cannot use that evaluation
[example: examples/books/defattach-exec.lisp]. The manual names three uses:
constrained function execution, sound modification of the ACL2 system, and
program refinement [:doc defattach].

### 2.9.5 Certification checks the boundary, and a local include is not an interface

Certification includes the book again after proving it: `certify-book` "may
roll back the logical world ... and perform an `include-book` to check for
`local` incompatibilities" [:doc certify-book], the analogue of
`encapsulate`'s second pass [:doc local-incompatibility].

What an includer gets is the non-local events, and only those.
`examples/books/lib.lisp` proves its exported theorem with a local lemma and
with the rules of a locally included `std/lists/take`;
`examples/books/user.lisp` includes it and checks, with `assert-event`, that
neither the local lemma nor `len-of-take` exists in its world, that the
exported theorem does, and that `sum-list` arrives disabled as the export
event left it [example: examples/books/lib.lisp],
[example: examples/books/user.lisp]. A `local` include is a private tool of
the book, not part of what it offers.

A non-local include is part of what it offers, and fn measured the cost. Its
ledger's "include hygiene" lint "flags a non-local `(include-book "x")` whose
target is a local book of this tree that ends with no theory withdrawal at
all ... Such an include is not an interface: it enables every rule `x` leaves
enabled in the includer and in everything that includes the includer. The
measured case is `books/bp-ingress.lisp`, which took a non-local include of
`article-properties` for a single guard hint and turned a six-minute proof
into an 1800 s timeout, 1.92M backchain frames of which none contributed;
making that include `local` is what the lint asks for"
[fn: docs/proofs.md:257 @3bbfc4dca].

### 2.9.6 fn's export discipline

"Every book ends with an explicit theory event. It withdraws the recognizers
of records and states, the initial state, the transitions and every lemma
that is proof vocabulary rather than a keystone. What remains enabled on
include is: keystones, record lemmas, list-recursive vocabulary (the
functions proofs induct on) and small glue predicates written in accessor
vocabulary" [fn: docs/proof-style.md:186 @3bbfc4dca]. The book's own
theorems come first, "proved before the export event, in the theory the book
built, so a book's own proofs never depend on what an includer happens to
have enabled, and an includer never inherits a rule it did not ask for. This
is what makes two green lanes merge green"
[fn: docs/proof-style.md:237 @3bbfc4dca]. `examples/books/lib.lisp` ends with such an event
[example: examples/books/lib.lisp].

What may not leave a book: "record accessors, constructors and shapes;
recognizers of records and states; initial states; transitions; `len`-,
`consp`- or `true-listp`-backchaining rules; `-is-`/`-of-` equalities other
than record lemmas; proof-vocabulary lemmas ...; corollaries; anything an
includer would have to `disable` to keep its own proofs stable"
[fn: docs/proof-style.md:529 @3bbfc4dca].

The measurement behind it: `tools/rule_cost.py` "`ld`s every book under
`accumulated-persistence` on a farm box and ranks each exported rune by the
useless frames its includers spent on it ... On the whole tree that day, 668M
of 1.50G frames were useless tries of rules another fn book exported"
[fn: docs/proof-style.md:537 @3bbfc4dca]. The repair withdraws the worst
rules "at the END of the defining book (its own proofs keep them)", and gives
an includer that then fails "a local enable after its header includes, never
after a mid-book include"; enabling a withdrawn rule everywhere the profile
had once seen it useful was not a restoration, since "a book-wide enable turns
on a rule an intermediate book had already disabled: served-catalog +144,428
steps" [fn: docs/proof-style.md:542 @3bbfc4dca]. And the exception that the
loop pair of section 2.5.2 is: a rule "never-useful by the profile yet
load-bearing" [fn: docs/proof-style.md:549 @3bbfc4dca].

## 2.10 Books and certification

### 2.10.1 What certification does

"A **book** is a file of ACL2 forms", some marked `local`; `include-book`
"extends the logic of the host world by adding just the non-local events in
the book", and "assumes the events in a book are valid, so if you include a
book that contains an inconsistency (e.g., an inadmissible definition) then
the resulting theory is inconsistent!"; certification guarantees that
"successful inclusion is consistency preserving" [:doc books].

`certify-book` "(1) reads the forms in the book, confirming that the
appropriate packages are defined in the certification world; (2) does the
full admissibility checks on each form ...; (3) may roll back the logical
world ... and perform an `include-book` to check for `local`
incompatibilities ...; (4) writes a certificate recording not only that the
book was certified but also recording the commands necessary to recreate the
certification world ... and a book-hash for each of the books involved ...;
and (5) compiles the book if so directed" [:doc certify-book]. Every included
book must already be certified: "An error will occur if `certify-book` has to
deal with any uncertified book other than the one on which it was called"
[:doc certify-book]. Certification runs "as though
`(set-guard-checking t)` has been evaluated", and requires the default
defun-mode to be `:logic` [:doc certify-book].

### 2.10.2 `include-book`

`(include-book "arithmetic/top-with-meta" :dir :system)` includes a community
book; `:dir :system` resolves the name in the installation's `books/`
directory [:doc include-book]. A book with no valid certificate is included
"anyway", with a warning, which "can lead to serious errors"; the
`:uncertified-okp`, `:defaxioms-okp` and `:skip-proofs-okp` arguments, all
`t` by default, turn those conditions into errors when `nil`
[:doc include-book]. The best practice: "Use relative paths in `include-book`
events only when including books contained within the same library.
Otherwise, use `:dir :system`. Never use absolute paths" [:doc best-practices].

### 2.10.3 The portcullis, `.acl2` files, `defpkg`

The certificate's portcullis holds the ACL2 version, "a list of commands used
to create the ``certification world'' and an alist specifying book-hash values
for all the books included in that world"; `include-book` must re-execute
those commands, skipping proofs and local events, before it can even read the
book [:doc portcullis]. "Clearly, a book is most useful if its certification
takes place with as few non-local events as possible that extend the initial
logical world" [:doc portcullis].

`defpkg` forms "should not occur in books" [:doc defpkg]; they belong in the
portcullis. With `cert.pl` that means an `.acl2` file: "First, if a file named
`foo.acl2` exists, then it will be used. Else, if a file named `cert.acl2`
exists, then it will be used" [books: build/doc.lisp:558]. `cert.pl` also
loads the `.port` file of each included book before certifying, "the
portcullis (`.port` file) of each included book" [books: build/doc.lisp:558].
This guide's `examples/books/user.cert` records, in its portcullis, the
include-books of `std/portcullis` and `cowles/portcullis` that `cert.pl`
loaded that way for `std/testing/must-fail` [measured: `head -c 600
examples/books/user.cert` after `examples/certify.sh books/user.lisp`, laptop,
ACL2 8.7 / SBCL 2.6.8]. For new packages the community's recipe is a
`package.lsp` loaded by a `portcullis.acl2` for an empty `portcullis.lisp`
book, and a `cert.acl2` that includes that book, so that the certificates of
many books share one redundant `include-book` instead of each re-checking the
`defpkg` [:doc working-with-packages]. File extensions carry the
distinction: `.lisp` for certifiable books, `.acl2` for certification
commands, `.lsp` for other Lisp files [:doc file-extensions].

### 2.10.4 The products

Certifying `inc.lisp` with `cert.pl` leaves `inc.cert`, "the ACL2 certificate";
`inc.cert.out`, "the log for certifying `inc`"; a compiled file whose
extension depends on the Lisp; and `Makefile-tmp`, "a Makefile that `cert.pl`
generated" [books: build/doc.lisp:297]. `certify-book` writes `B.port`, "all
of the portcullis commands for `B`", used when `B` is included uncertified
[:doc certify-book]. On SBCL the compiled file is `.fasl`, loaded by a later
`include-book` "provided the compiled file has a later write date than the
source file" [:doc certify-book]; `include-book` itself requires it to be
"more recent than the book's certificate" [:doc include-book]. This guide's
examples leave exactly `.cert`, `.cert.out`, `.fasl` and `.port` beside each
book, and `Makefile-tmp` in `examples/` [measured: `ls examples/books/` after
certification, laptop, ACL2 8.7 / SBCL 2.6.8].

fn's cache learned the date rule the hard way: "ACL2 on SBCL writes
`book.fasl` after the certificate and include-book loads it only when it is
not older than the `.cert`, so a book installed with a pair alone loads
uncompiled", so fn's certificate cache stores the `.fasl` with the
`.cert`/`.port` pair and dates it no earlier than the certificate
[fn: docs/proofs.md:351 @3bbfc4dca].

### 2.10.5 `cert.pl`

"If your book includes supporting books that aren't certified, `cert.pl` will
rebuild exactly the necessary books, in parallel" [books: build/doc.lisp:34].
`-j N` sets parallelism, with the warning that memory, not only CPU count,
bounds it; `-k` keeps going after a failure; `-p` certifies only a book's
dependencies [books: build/doc.lisp:297]. The dependency scanner is "a dumb
Perl script. It's quite easy to fool it using macros or other tricks. But you
don't even need to get that fancy -- a newline will do the trick": an
`include-book` with the book name on the next line is invisible to it, which
is documented and relied on [books: build/doc.lisp:297].
`examples/certify.sh` is a thin wrapper that runs `cert.pl` with the laptop
ACL2 under a machine-wide lock.

### 2.10.6 Book hashes, and what a change costs

"By default, a book-hash is an alist that records, for a given book (`.lisp`
file), its file size (in bytes) and its write-date"; setting
`ACL2_BOOK_HASH_ALISTP` to `NIL` before starting ACL2 makes it a checksum,
"which gives a bit greater security" at some cost in certification and
inclusion time [:doc book-hash]. fn sets it everywhere: "Every fn tool that
starts ACL2 sets `ACL2_BOOK_HASH_ALISTP=NIL`, so ACL2 8.7 hashes book
*contents* rather than write dates and absolute paths: a `.cert`/`.port` pair
is valid in any worktree and on any host whose book content matches"
[fn: docs/proofs.md:295 @3bbfc4dca]. Its cache's key is the closure, not the
book: "a certificate is valid only for a book *and every book it includes*,
so the key is the SHA-256 of the sorted `<path>:<sha256>` listing of the book
and its whole local include closure" [fn: docs/proofs.md:308 @3bbfc4dca].

So "changing a book recertifies every book that includes it"
[fn: docs/proof-style.md:445 @3bbfc4dca]. fn's measurement of form-level
hashing: "a comment or layout edit to a wide book recertifies nothing ... a
docstring is part of a form and counts"
[fn: docs/proof-style.md:447 @3bbfc4dca]. Its rule for where new things go: look the book up in the table
`tools/shape_books.py` generates and "Prefer a new book low in the table over
a new field high in it" [fn: docs/proof-style.md:451 @3bbfc4dca]. Its record
generator carries the warning in its own text: "a change to
`books/defrecord.lisp` --- a comment included --- invalidates its certificate
and every certificate above it, so batch such changes"
[fn: docs/proof-style.md:147 @3bbfc4dca].

### 2.10.7 Provisional certification

Provisional certification splits certification into three procedures:
Pcertify (or Create), which skips proofs and writes `bk.pcert0`; Convert,
which does the proofs and writes `bk.pcert1`; and Complete, which renames
`bk.pcert1` to `bk.cert` once every included book has a `.cert`. "The main
idea of provisional certification is to break sequential dependencies caused
by `include-book`, that is, so that a book's proofs are carried out even when
it includes books ... that have not themselves been fully certified"
[:doc provisional-certification]. `cert.pl --pcert-all -j 4` runs it
[:doc provisional-certification].

The manual's trust statement: "Provisional certification makes it a bit easier
for a determined user to subvert correctness. For example, the Complete
procedure only checks write dates to ensure that each sub-book's `.cert` file
is no older than the corresponding `.lisp` file, but it does not look inside
`.cert` files of sub-books ... for maximum trust, it is best for all books in
a project to be certified from scratch without the provisional certification
process" [:doc provisional-certification].

fn uses it as a triage instrument and only that. An ordinary closure run
stops at the first red book, and every book above reads "There is no
certificate on file", so "one run names one *layer* of independent reds";
a provisional round does every book's proofs in one parallel Convert wave
[fn: docs/proofs.md:554 @3bbfc4dca]. On a 63-book closure "an ordinary round
took 690.8 s and named one independent red with fifteen books cascading
behind it; one provisional round took 317.3 s and named four independent reds
and twelve proved-but-blocked books" [fn: docs/proofs.md:574 @3bbfc4dca].
And: "**A triage run is evidence of nothing but its list of reds** ...
Provisional certification is a discovery instrument for the same reason ACL2
says it is: Complete checks sub-books' certificate write dates rather than
their book-hash" [fn: docs/proofs.md:588 @3bbfc4dca].

### 2.10.8 `make-event` and `assert-event`

"In essence, the expression `(make-event form)` replaces itself with the
result of evaluating `form`", and unlike a macro the form may read and change
the state and world [:doc make-event]. In a book "it is expanded during book
certification but not, by default, when the book is included": the expansion
"is recorded in the book's certificate and re-used during a subsequent
`include-book`", unless `:check-expansion t` asks for it to be redone and
compared [:doc make-event]. `examples/books/make-event-check.lisp` uses it
to refuse certification unless a check holds and to record a constant
computed from the world at certification time
[example: examples/books/make-event-check.lisp].

`(assert-event form)` is the event form of a check: "Calls of `assert-event`
are event forms; thus, they may occur in books as well as `encapsulate` and
`progn` events", causing an error when the form evaluates to `nil`; it is
skipped when proofs are skipped (during `include-book`, for instance) unless
given `:on-skip-proofs t` [:doc assert-event]. The examples of this guide use
it for counterexamples and for checks on the world, such as the absence of a
local lemma [example: examples/prover/false-conjecture.lisp],
[example: examples/books/user.lisp].

### 2.10.9 `must-fail` and `must-succeed`

`std/testing/must-fail` "Ensures that a command which returns an error-triple
-- e.g., `defun` or `defthm` -- will not be successful"; by default only a
soft error counts, `:expected :hard` or `:any` widen that
[books: std/testing/must-fail.lisp:17]. Its caveat: "If a book contains a
non-local form that causes proofs to be done, such as one of the form
`(must-fail (thm ...))`, then it might not be possible to include that book
... One fix is to make such forms local" [books: std/testing/must-fail.lisp:17];
every `must-fail` in this guide's examples is local for that reason.
`must-succeed` is the converse, and runs its form inside a `make-event`, so a
`defun` checked by it "doesn't persist after the `must-succeed` form"
[books: std/testing/must-succeed.lisp:17].

In this guide a `must-fail` records a failed first attempt, bounded by a
step limit where the failure would be slow [example:
examples/prover/induction-lemma-first.lisp]. A rewrite loop inside one ends
at the call-depth limit and still counts as a failure; the loop examples
certify that way [example: examples/rewriting/loop-pair.lisp].

**Pitfall: a failed proof is not a counterexample.** fn's rule for the
witnesses ("teeth") that accompany a keystone theorem: "Never a general
negated `must-fail`: it proves that the prover could not find a proof, which
is not a counterexample, and it loops when the negation is unprovable rather
than false" [fn: docs/proof-style.md:381 @3bbfc4dca]. Teeth are concrete
violating values checked by `assert-event`; a `must-fail` of a weakened
statement, where no value can be evaluated, is labelled `; teeth:
prover-refusal REASON` and counted apart
[fn: docs/proof-style.md:389 @3bbfc4dca]. fn's ledger flags a `must-fail` "whose body is a bare
`thm`/`defthm` whose statement mentions no constant ... so it refutes a
general claim rather than a specific violating value"
[fn: docs/proofs.md:254 @3bbfc4dca].

### 2.10.10 `set-enforce-redundancy`, `comp`

`(set-enforce-redundancy t)` makes most non-redundant events an error; it is
local to the book, and guarantees that a book's definitions and theorems are
copies of ones proved elsewhere, which the manual describes for `rtl/rel4`'s
`lib/` books whose proofs live in `support/` [:doc set-enforce-redundancy].

`(comp t)` compiles user functions; it is "generally not necessary to place
the form `(comp t)` ... in a book, because `certify-book` compiles the raw
Lisp definitions anyhow, by default", but `(comp :exec)` compiles executable
counterparts, which matters for functions whose guards are not verified
[:doc comp].

### 2.10.11 The best-practices list, where it applies

Quoted from [:doc best-practices]:

- "Top-level `include-book` and `in-theory` events should be at the top of
  the book." (section 2.8.6)
- "`include-book` and `in-theory` events should be local where possible,
  unless they support the main purpose of the book and are intended to be
  ``exported.''" (section 2.9.5)
- "Most functions (especially non-recursive function) should be disabled by
  default." (section 2.8.6)
- "Sets of rules which are known to cause rewrite loops should be declared
  incompatible as a theory-invariant." (section 2.5.2)
- "Try to avoid subgoal hints." (chapter 1, section 1.8.1)
- "Avoid short proof timeout windows ... use step limits instead."
  (chapter 1, section 1.10)
- "A book should use either `defthm` or `defrule`, not both", and likewise
  `defun` or `define`.

## 2.11 Example index for this chapter

| example | technique |
| --- | --- |
| `examples/rewriting/loop-pair.lisp` | a pair of rules that loop; the normal-form choice; `theory-invariant` |
| `examples/rewriting/loop-stopper.lisp` | a permutative rule with and without its loop-stopper |
| `examples/rewriting/syntaxp.lisp` | a self-feeding rule stopped by `syntaxp` |
| `examples/rewriting/free-variables.lisp` | `:match-free :once` against `:all` |
| `examples/rewriting/bind-free.lisp` | binding a free variable with `bind-free` |
| `examples/rewriting/forward-chaining.lisp` | the same implication as rewrite and as forward-chaining rule |
| `examples/rewriting/linear.lisp` | a bound as a `:linear` rule |
| `examples/rewriting/force.lisp` | a forced hypothesis and its forcing round |
| `examples/rewriting/congruence.lisp` | `defequiv`, `defcong`, rewriting under an equivalence |
| `examples/rewriting/induction-rule.lisp` | the `:induction` rune and an `:induction` rule |
| `examples/rewriting/definition-rule.lisp` | an alternative `:definition` |
| `examples/rewriting/compound-recognizer.lisp` | a compound recognizer, and tau doing the same job |
| `examples/rewriting/theories.lisp` | runic designators, `deftheory`, `ground-zero`, executable counterparts |
| `examples/books/lib.lisp`, `examples/books/user.lisp` | what `local` hides; an export theory |
| `examples/books/encapsulate-fi.lisp` | constrained function, generic theorem, two functional instances |
| `examples/books/defattach-exec.lisp` | executing a constrained function through an attachment |
| `examples/books/make-event-check.lisp` | certification-time checks and constants |
