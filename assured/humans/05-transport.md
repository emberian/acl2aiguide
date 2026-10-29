# 5. Transport across representations

A negative test can pass without testing the mathematics. In the transport
experiment, a `must-fail` around a functional instance accepted a malformed
lambda. The recorded diagnostic was:

```text
is neither a function symbol nor a pseudo-lambda expression
```

The repair was a named observation function, an unwrapped run whose failure
was inspected, and a separate witness falsifying the intended obligation.
A refusal alone was not the tooth.
[guide: examples/transport/README.md:193]
[example: examples/transport/read-state-teeth.lisp]

Nor does successful transport establish a saving. Experiment B's pessimistic
result, for its logical cursor-row example on ACL2 8.7 on the laptop, was
**72 hand-written code lines for 71 generated lines of statements and
definitions**. Its README says: "72 lines were written to obtain 71 lines
of statements." Generated proof instructions were excluded from that
comparison.
[guide: examples/transport/README.md:113]
[guide: examples/transport/README.md:130]
[fn: build/coordinator/fn2/TRANSPORT.md:548 @worktree, read 2026-10-29]

The useful result is narrower: a reusable theorem can carry a relation
through every future event suffix, and an isomorphism with base-function
correspondences can carry client functions and theorems to another
representation. Those are two different mechanisms, demonstrated by
Experiments A and B.
[fn: build/coordinator/fn2/COHERENCE.md:794 @worktree, read 2026-10-29]

## 5.1 Why transport matters before migrations exist

A representation project can solve the wrong problem. fn2's transport note
initially missed its standing decision against pre-release migration and
compatibility obligations. Its corrected section 0 separates moving stored
data between releases from preserving proofs across development revisions:
wiping data does not repair the clients' theorems.
[fn: build/coordinator/fn2/TRANSPORT.md:27 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/TRANSPORT.md:31 @worktree, read 2026-10-29]

Two rows of the coherence inventory identify the work that remains useful.
Q4 is a fold versus the summary replacing its retained history; Q23 is a
logical table row versus another representation of that row. Q4 asks about
every event kind and future suffix. Q23 asks about the users and theorems
in the propagated range. Both rows report proofs on examples, not completed
integration into the server.
[fn: build/coordinator/fn2/COHERENCE.md:55 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:74 @worktree, read 2026-10-29]

The distinction reaches the implementation. At the pinned fn2 revision,
`columns.lisp` generates array storage and describes its row/table views as
non-executable. Its column predicates already use a constrained-function
template to share list proofs. A theorem about an alist cursor therefore
demonstrates a transport technique without establishing the missing
connection to served column operations.
[fn: fn2/books/columns.lisp:1 @127f7b877]
[fn: fn2/books/columns.lisp:17 @127f7b877]
[fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29]

## 5.2 Functional instantiation carries the induction

Copying a proof leaves every representation paying for the same induction.
The earlier fn `def-loop` lesson recommends: "When the same proof recurs,
prove it once over constrained functions and obtain each instance by
functional instantiation". Its implementation proves a bridge per loop
shape and instantiates that bridge for generated loops.
[guide: fn-lessons/22-def-loop.md:60]
[fn: books/def-loop.lisp:14-21 @3bbfc4dca]

ACL2 describes functional instantiation as "An analogue in ACL2 of
higher-order logical reasoning." An `encapsulate` introduces function
signatures, supplies local witness definitions, and exports proved
constraints while hiding those definitions. Subsequent generic theorems
depend on the exported constraints.
[:doc functional-instantiation] [:doc encapsulate]

The instance does not get those premises for free. The manual says that
before a functional instance can be used, ACL2 generates:

> proof obligations arising from the replacement of the `fi`'s by the
> `gi`'s in constraints that ``support'' the lemma to be functionally
> instantiated

The syntax is `(:functional-instance lmi (f1 g1) ... (fn gn))`; substitutions
replace functions, including the relation when it is a constrained
parameter.
[:doc lemma-instance]
[example: examples/transport/read-state-transport.lisp]

Experiment A puts that relation in the interface as `fc-rel`, beside two
initializers, steps, observations, and admissibility predicates. Its
constraints establish related admissible initial states, preservation of
admissibility and relation by a step, and equal observations at related
admissible states.
[example: examples/transport/fold-contract.lisp]

The induction is then written once:

```lisp
(defthm fc-rel-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))
```

Its companion `fc-obs-fold` concludes equal observations after the suffix.
Both apply to any related admissible starting pair, not only the initial
states.
[example: examples/transport/fold-contract.lisp]

## 5.3 The relation must survive the next observation

Equal answers now can conceal a difference the next event exposes.
The histories `((:read 1))` and `((:read 2))` each report one read article
up to bound 2. After `(:read 1)`, their counts are respectively 1 and 2.
The example evaluates these exact results and proves
`rs-count2-rel-step-obligation-false`, falsifying the instantiated step
obligation at that pair.
[example: examples/transport/read-state-teeth.lisp]

fn2's experiment proposal got this detail wrong: it called the weak
relation equality of counts "at every bound", then supplied equality only
at bound 2. The certified example uses the fixed-bound relation
`rs-count2-rel`. The tooth establishes that this relation needs strengthening;
it does not establish that every observational interface needs a strictly
stronger relation.
[fn: build/coordinator/fn2/TRANSPORT.md:282 @worktree, read 2026-10-29]
[example: examples/transport/read-state-teeth.lisp]

The positive instance retains history newest first and observes whether an
article is read, or how many articles are read through a bound. Its summary
is `(hwm . above)`: a read prefix and a sorted list above that prefix,
compacted after each event. The relation quantifies over article queries:

```lisp
(defun-sk rs-same-reads (h s)
  (forall n (equal (rs-h-obs-read h n) (rs-s-obs-read s n))))
```

[example: examples/transport/read-state-history.lisp]
[example: examples/transport/read-state-summary.lisp]
[example: examples/transport/read-state-transport.lisp]

The instance proves preservation for `:read`, `:catchup`, and malformed
events. Malformed events are retained by the history step but contribute
nothing to its observation; the summary step leaves its state unchanged.
Agreement on counts then follows from agreement on every article, by
induction on the bound in `rs-obs-count-agree`.
[example: examples/transport/read-state-history.lisp]
[example: examples/transport/read-state-summary.lisp]
[example: examples/transport/read-state-transport.lisp]

Here is the entire transported theorem and its hints:

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

This theorem does not establish that a converter produces a related pair.
That is `rs-summarize-related`; combining it with adequacy yields
`rs-summarize-adequate`. The bad-compaction control also matters: after
`(:read 1) (:read 3)`, the mutant reports article 2 read, while history and
the correct summary report `nil`.
[example: examples/transport/read-state-transport.lisp]
[example: examples/transport/read-state-teeth.lisp]

## 5.4 A smaller certificate: the converter graph up to congruence

Requiring the converter to commute with steps by exact equality can reject
an adequate summary. The counterexample in `UNIVERSAL-CONSTRUCTIONS.md`
summarizes a counter as `(n mod 2, 0)`: an unobserved second component changes
during summary execution. Exact homomorphism is sufficient for adequacy,
but this example shows that it is not necessary.
[fn: build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:106 @worktree, read 2026-10-29]

Nor is an arbitrary "up-to" simplification safe to compose. Pous and
Sangiorgi explain that sound up-to functions are not generally closed under
composition. Their stronger condition is compatibility: for monotone
functions, `f o b <= b o f`. Compatible functions are sound and remain
compatible under composition and pointwise union.
[paper: pous-sangiorgi2019-bisimulation-and-coinduction-enhancements-historical-perspective.pdf, section 5, pp. 7-8]

For the deterministic fold here, the concrete technique is the converter
graph up to an equivalence on summaries. That equivalence respects both the
summary step and its observations. `HIGHER-STRUCTURES.md` proposes this
second certificate form; the certified implementation names its fold
theorem `gu-graph-upto-fold`.
[fn: build/coordinator/fn2/HIGHER-STRUCTURES.md:182 @worktree, read 2026-10-29]
[example: examples/assured/summary-upto.lisp]

ACL2 already has the proof interface. `defequiv` generates a theorem that
the relation is "Boolean, reflexive, symmetric, and transitive".
For `defcong`, the manual requires its two relations to be "known
equivalence relations"; the event proves preservation at a specified
argument position. Congruence rules tell the rewriter which equivalence
to maintain while simplifying that argument.
[:doc defequiv] [:doc defcong] [:doc congruence]

The complete generic encapsulation is:

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

Starting from `s` equivalent to `gu-conv(h)`, step congruence carries that
equivalence through the summary step. The step equation connects the result
to conversion of the extended history. Transitivity closes the step;
observation congruence and `gu-edge` give equal answers. This is the
compatible up-to technique embodied by `defequiv` plus these `defcong`
rules, with the converter equations supplied.
[example: examples/assured/summary-upto.lisp]
[fn: build/coordinator/fn2/HIGHER-STRUCTURES.md:182 @worktree, read 2026-10-29]

The book separates the two resulting theorems:
`gu-graph-upto-fold` preserves equivalence to the converted history;
`gu-graph-upto-obs` gives equal observations. Its constraints are
unconditional, unlike Experiment A's explicitly admissibility-guarded
contract. This smaller certificate removes the quantified relation, but
does not remove the equivalence, congruence, step, or observation proofs.
[example: examples/assured/summary-upto.lisp]

The parity instance uses `(parity . steps)`. Only `:inc` extends the history
and flips parity; every summary step increments `steps`, including a
`:noop`. Conversion resets `steps` to zero, and `par-equiv` ignores it.
`par-summary-adequate` instantiates `gu-graph-upto-obs`; the exact-equality
claim is refuted separately:

```lisp
(defthm parity-step-not-homomorphism
  (not (equal (par-s-step (par-conv nil) :inc) (par-conv (par-h-step nil :inc))))
  :hints (("Goal" :in-theory (enable par-s-step par-conv par-h-step))))
```

The positive assertion states exactly these results:

```lisp
(assert-event
 (let ((j '(:inc :noop :inc :inc :noop)))
   (and (equal (par-s-obs (par-s-fold (par-conv nil) j) :parity) 1)
        (equal (par-h-obs (par-h-fold nil j) :parity) 1)
        (equal (cdr (par-s-fold (par-conv nil) j)) 5))))
```

[example: examples/assured/summary-upto.lisp]

## 5.5 Isomorphisms carry clients, after the base correspondence

An isomorphism declaration alone does not translate a client's accessors.
`propagate-iso` consumes translated base functions and correspondence
theorems in both directions. Its manual describes substitution through
function bodies and theorem statements, and states: "Currently does not
handle mutual recursion."
[:doc apt::propagate-iso]

Experiment B starts with a logical row containing registration, position,
and generation. Position and generation are u60 values. The new row splits
position into epoch and sequence, with `position = epoch * 2^32 + seq`;
its epoch is restricted to u28 and its sequence to u32.
[example: examples/transport/cursor-v1.lisp]
[example: examples/transport/cursor-iso.lisp]

`defiso` is a specialization of `defmapping` with both inverse-theorem
options set to `t`. Its implementation passes those options to the mapping
generator; it does not supply the correspondence of arbitrary clients.
[:doc defiso]
[books: std/util/defiso.lisp:58]

After the maps and base functions, the example declares the isomorphism
and, among its correspondence theorems, this pair:

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

The transformation names the supplied correspondences and its event range:

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
```

It generates the new advance and token-check functions, transported
theorems, and function correspondences. The example checks that
`cur2-advance-monotone`, `cur2-advance-idempotent`, `cur2-advance-rowp`,
and `cur2-advance-keeps-token` exist as theorems.
[example: examples/transport/cursor-iso.lisp]

## 5.6 Controls and three findings from propagation

Widening the epoch to u32 breaks the backward image condition.
The wide row with epoch `2^28` and sequence 0 converts to position `2^60`,
outside the old u60 domain. `cur2-wide-beta-image-false` proves the
obligation false at that row. The book records the unwrapped diagnostic:

```text
The proof of the :BETA-IMAGE applicability condition fails
```

[example: examples/transport/cursor-wide.lisp]

The manual's obligation is: "The conversion [beta] maps the domain [B]
to the domain [A]" (brackets replace its mathematical symbols).
The control sets `:guard-thms nil` to isolate this image failure.
Its witness is a theorem, because evaluating the conversion at that row
would violate the conversion's narrower guard.
[:doc defmapping]
[example: examples/transport/cursor-wide.lisp]

Dropping generation fails differently, at `:beta-of-alpha`.
The manual states that beta "is left inverse of" alpha. Here conversion
back supplies generation zero, so it cannot recover arbitrary old rows.
Two admissible rows with registration 7, position 100, and generations
5 and 6 have one new image but disagree on accepting token 5.
`no-v3-token-check` proves that an unconstrained function of the new row
and token cannot agree with both old answers.
[:doc defmapping]
[example: examples/transport/cursor-v3-lossy.lisp]

Three findings determine the shape worth copying:

- **Domain hypotheses.** The experiment first tried an unconditional
  generation theorem and propagation failed. Its certified statement
  includes `(cur1-p row)`, even though the old equation holds more broadly.
  The transported proof uses the domain where the isomorphism applies.
  [example: examples/transport/cursor-v1.lisp]
  [fn: build/coordinator/fn2/TRANSPORT.md:560 @worktree, read 2026-10-29]
- **Names from predicates.** The naming code substitutes the codomain
  predicate's name for the domain's, removing a trailing `-P` when both
  have one. Thus `cur1-p` and `cur2-p` produce the intended client names.
  [books: kestrel/apt/lift-iso.lisp:827]
  [example: examples/transport/cursor-v1.lisp]
- **Disabled correspondences.** In this experiment, enabling a forward
  correspondence caused rewriting through its own conversion map.
  The completed book stores all six base correspondences as `defthmd`.
  The community test likewise disables its reverse correspondence.
  [fn: build/coordinator/fn2/TRANSPORT.md:562 @worktree, read 2026-10-29]
  [example: examples/transport/cursor-iso.lisp]
  [books: kestrel/apt/propagate-iso-test-1.lisp:115]

## 5.7 Count the consumers and keep the boundary

A registration form can conceal work rather than remove it. The coherence
note explicitly distinguishes A's composition template from B's
transformation template: `fc-rel-fold` is not B's composition engine.
A still supplies event lemmas, converter correctness, and observation
work; B still supplies domains, inverse laws, and base correspondences.
[fn: build/coordinator/fn2/COHERENCE.md:789 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:794 @worktree, read 2026-10-29]

The recorded 72-for-71 result supports counting before generating another
DSL. Base correspondence work grows with base functions; propagated work
grows with their users and theorems. The proposed generator extension is
promising where users far outnumber base functions, but that ratio remains
to be measured on the real table families.
[fn: build/coordinator/fn2/TRANSPORT.md:555 @worktree, read 2026-10-29]

Summary adequacy covers future observations of the retained contract; it
does not establish which historical answers storage keeps available.
Cursor transport covers logical rows; it establishes neither their
correspondence to served columns nor scaling to generated accessor
families. These are the experiments' stated boundaries.
[fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29]
