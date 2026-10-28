# Lane A: the logic and the prover; rewriting, theories and books

Read `/Users/ember/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `humans/01-logic-and-prover.md`
- `humans/02-rewriting-theories-books.md`
- `examples/prover/*.lisp`, `examples/rewriting/*.lisp`, `examples/books/*.lisp`

## Chapter 1: the logic and the prover

What ACL2 is: a first-order logic of total recursive functions over a fixed
universe (numbers, characters, strings, symbols, conses), the definitional
principle (termination by a measure and a well-founded relation; the
admission obligations), the induction principle, the relation to Common Lisp
(every function executes; `:logic` vs `:program` mode); the waterfall
(preprocess, simplify with the rewriter, destructor elimination,
fertilization/cross-fertilization, generalization, elimination of
irrelevance, induction) and what each stage prints
[`introduction-to-the-theorem-prover`, `acl2-tutorial`, `the-method`,
`hints-and-the-waterfall`, `induction`, `defun`, `measure`, `ordinals`,
`:program`/`:logic`, `mutual-recursion`].

Why proofs fail and how to read a failed proof: the key checkpoint(s) and
`set-gag-mode`; reading a checkpoint's clause (which hypotheses are present
and in what normal form; a `(not (equal ...))` hypothesis is a rewrite that
did not fire; `hide`; `(if ... ) ` splits); the induction scheme chosen and
why it was wrong ("The Method"); when the goal is false (test it with
ground evaluation first); the `Time:` line (`prove`, `print`, `other`) and
what `other` means [fn docs/proof-style.md section 9.1]; `Prover steps
counted`; `accumulated-persistence`, `dmr`, `pstack`, `break-rewrite`
(`:brr t`, `:monitor`, `:go`, `:eval`), `(cw-gstack)`; `:pe`, `:pl`, `:pr`,
`:pbt`, `:ubt`. Then every kind of hint, each with a shape to copy and a
real failed-then-fixed example: `:use` with `:instance` and `:functional-instance`
(and the "use adds a hypothesis, it does not rewrite" pitfall), `:cases`,
`:expand`, `:induct`, `:in-theory` (`enable`, `disable`, `e/d`), `:do-not`,
`:do-not-induct`, `:nonlinearp`, `:by`, `:restrict`, `:clause-processor`,
computed hints and `set-default-hints`; the rule from fn docs/proof-style.md
9.3: a `Goal` `:in-theory` does not survive a subgoal that has its own
[`hints`]. Induction schemes: how ACL2 picks one, how to supply one with a
recursive function whose recursion matches, `tools/flag` for mutual
recursion, "merge" of schemes, the "induct on the right variable" rule.
Step limits and time limits (`set-prover-step-limit`,
`with-prover-time-limit`) and the pitfall from fn docs/proof-style.md 9.2
(an aborted probe measures nothing). `skip-proofs` and what it means
(certified vs. not; `:doc skip-proofs`), `defaxiom` (never), trust tags.

## Chapter 2: rewriting discipline, theories, books

Rule classes and how each is used: `:rewrite` (the left-hand side, the
hypotheses, backchaining, the `backchain-limit`, `:loop-stopper`,
`syntaxp`, `bind-free`, `case-split`, `force` and `case-split-limitations`),
`:type-prescription`, `:forward-chaining` (`:trigger-terms`; why fn uses it
for shape facts and not rewrite [fn docs/proof-style.md section 1]),
`:linear` (`:trigger-terms`; the fn note: a `:linear` with `:trigger-terms`
and `:rewrite` on one conclusion crashed SBCL, split them [fn
docs/proof-style.md last lines]), `:definition`, `:elim`, `:equivalence`,
`:congruence`, `:refinement`, `:meta`, `:induction`, `:compound-recognizer`,
`:tau-system`, `:rule-classes nil` [`rule-classes`, `rewrite`,
`loop-stopper`, `free-variables`, `forward-chaining`, `type-prescription`,
`linear`, `meta`, `bind-free`, `syntaxp`, `case-split`, `force`,
`backchain-limit`, `tau-system`]. Free variables in hypotheses and the three
ways they bind (`:match-free :all/:once`, binding hypotheses, `bind-free`).
Loops: how to see a loop (`:brr`, `accumulated-persistence`), loop-stoppers,
the pair of rules that rewrite each other (fn: `fn-lgw-slice-is-take` and
`fn-lg-slice`, docs/proof-style.md section 8). Normal forms and conventional
normal forms [`doc/practices.lisp` `conventional-normal-forms`]. The theory:
`enable`/`disable`/`e/d`, `deftheory`, `in-theory`, `current-theory`,
`minimal-theory` and `ground-zero`, `theory-invariant`, `:executable-counterpart`
runes, `(:d f)`/`(:e f)`/`(:t f)`, `set-non-linearp`, and the tau system
(when it is the time sink: fn's `tau_cost.py` measurement, docs/proof-style.md
9.1) [`theories`, `theory-management` in doc/practices.lisp, `in-theory`,
`deftheory`, `theory-invariant`, `rune`]. `local` and the local/non-local
boundary: what `encapsulate` exports, constrained functions and their
witnesses, `defattach`, the "two-pass" certification and why a local
include is not an interface [`local`, `encapsulate`, `defattach`,
`certify-book`]; fn's export discipline (every book ends with an explicit
theory event; what may leave a book enabled; `rule_cost.py`'s measurement
of 668M useless frames of 1.50G) [fn docs/proof-style.md sections 2 and 8].
Books and certification: `certify-book`, `include-book` (`:dir :system`),
the portcullis and `.acl2` files, `defpkg`, the `.cert`/`.port`/`.fasl`
products, `cert.pl` and `build::cert.pl` dependency scanning, `ACL2_BOOK_HASH_ALISTP`
content hashing [fn docs/proofs.md "Certificates"], the include-closure
cost (a change low in the graph recertifies everything above:
docs/proof-style.md "Shape books"), provisional certification (`.pcert0`/
`.pcert1`) as a triage instrument and why not as trust [fn docs/proofs.md,
`provisional-certification`], `make-event` and `assert-event`,
`must-fail` and `must-succeed` from `std/testing`, `set-enforce-redundancy`,
`comp` and compilation. `best-practices` from doc/practices.lisp,
quoted where it applies.

## Examples to write and certify (examples/prover, examples/rewriting, examples/books)

At least: an induction proof whose first attempt fails and the fix (`:induct`
or a better lemma); a `:use` that needs `:instance`; a `:cases` split; an
`:expand`; a loop-stopper demonstration (two rules that loop and the fix,
using `must-fail` with `with-prover-time-limit` or a step limit so it
certifies); a free-variable hypothesis that fails to bind and the
`bind-free`/`:match-free` fix; a forward-chaining rule; a linear rule; a
`defthm` with `:rule-classes nil` used by `:use`; an `encapsulate` with a
constrained function and a `:functional-instance`; a two-book pair
(`lib.lisp` with a `local` lemma and an export theory, `user.lisp` that
includes it) showing what `local` hides; a book that uses `make-event` to
assert something at certification time. Each certifies via
`examples/certify.sh`.

## Report

READY with the two chapters, the examples' Built lines, the sources block and
the README lines; or BLOCKED.
