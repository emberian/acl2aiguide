# 09. Exported internals: the includer pays for every rule a book leaves on

## The wound

Measured on the tree before the 2026-09-19 realignment: "no typed structures
(806 raw-list accessors), 642 `-is-`/`-of-` equalities of which 68 were
`:rule-classes nil` and the rest were global rewrite rules on include,
whole-state recognizers recomputed on every served operation ..., general
negated `must-fail` teeth, and 116 reaches for `minimal-theory`. Each of those
is a symptom of the same thing: books exported their internals"
[fn: docs/proof-style.md:22-28 @3bbfc4dca]. The tree-wide cost, measured on
2026-09-28 by loading every book under `accumulated-persistence`: "668M of
1.50G frames were useless tries of rules another fn book exported"
[fn: docs/proof-style.md:537-542 @3bbfc4dca]. One non-local include "for a
single guard hint ... turned a six-minute proof into an 1800 s timeout, 1.92M
backchain frames of which none contributed" [fn: docs/proofs.md:262-265 @3bbfc4dca],
and a book-wide enable of the codec vocabularies "made every `:guard t`
definition pay for the open codec (`books/config.lisp`, minutes per form)"
[fn: docs/proof-style.md:751-754 @3bbfc4dca].

The symptom fn named, the reach for `minimal-theory`, grew rather than
shrank: 116 before the realignment [fn: docs/proof-style.md:27 @3bbfc4dca],
"2,145 reaches for `minimal-theory` in 381 books" on 2026-10-01
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:42-43 @worktree],
and 2,737 occurrences in 363 books at `origin/dev`, led by
`runtime-contract-isolation.lisp` (245), `post-transaction-sim.lisp` (117) and
`post-transaction.lisp` (94)
[measured: `git -C ~/dev/fn grep -o 'minimal-theory' 3bbfc4dca -- books | wc -l`, `grep -l ... | wc -l`, `grep -c ... | sort`, 2026-10-28, laptop].
These are counts of source text; they include the generators' own hint
templates (for example `books/def-loop.lisp:848`) and not their expansions.

## What was done about it

- The export discipline, now in chapter `humans/02-rewriting-theories-books.md`
  section 2.9.6: every book ends with an explicit theory event; what may stay
  enabled is keystones, record lemmas, list-recursive vocabulary and glue
  predicates; "A hint that reaches for `minimal-theory` is a book that
  exported too much; say which rules you mean with `e/d`"
  [fn: docs/proof-style.md:529-535 @3bbfc4dca].
- Records generated opaque by `fn-defrecord`, with the definitions withdrawn
  under `<record>-internals` and three forward-chaining shape facts exported
  in their place [fn: docs/proof-style.md:79-182 @3bbfc4dca].
- `tools/rule_cost.py` ranks exported runes by useless frames and `withdraw`
  disables the worst "at the END of the defining book (its own proofs keep
  them)"; enabling them back wherever the profile once saw them useful was
  not a restoration ("served-catalog +144,428 steps"), and 93 of 309 local
  enables were needed [fn: docs/proof-style.md:542-549 @3bbfc4dca].
- The ledger's export-hygiene and include-hygiene lints
  [fn: docs/proofs.md:239-268 @3bbfc4dca].

## The lesson

Decide a book's interface when you write the book, in its last event, and
prove the book's own theorems before that event in the theory the book built.
The prover's cost grows with what it knows: "Generally speaking, the more ACL2
knows, the slower it runs. That is because the search space grows with the
number of alternative rules" [:doc accumulated-persistence]. An includer that
needs a withdrawn rule enables it in the one hint that needs it, never
book-wide, because an `:in-theory` hint is "evaluated relative to the current
ACL2 logical world" [:doc hints] and a book-level `enable` turns rules on for
every later form. A `minimal-theory` hint is a symptom to trace to the book
that exported too much, not a cure.

## The shape to copy

The book-end event, as fn writes it [fn: docs/proof-style.md:198-226 @3bbfc4dca]:

```lisp
(in-theory (disable fn-articlep fn-pendingp fn-statep fn-initial-state
                    fn-install-pending fn-clear-pending
                    fn-accept-prepare fn-accept-complete fn-accept-recover))
                                            ; books/acceptance.lisp

(deftheory fn-acceptance-invariants-vocabulary
  '(fn-bump-preserves-nexts fn-next-positive ... fn-watermark-pair-not-below-member))
(in-theory (disable fn-acceptance-invariants-vocabulary))
                                            ; books/acceptance-invariants.lisp
```

and the includer's one-line, local re-enable of exactly that vocabulary:

```lisp
(local (in-theory (enable fn-acceptance-invariants-vocabulary ...)))
                                            ; books/node-invariants.lisp
```

A certified example of a library that exports one theorem and keeps its
helpers is `examples/books/lib.lisp` with its includer `examples/books/user.lisp`
[example: examples/books/lib.lisp], [example: examples/books/user.lisp]. To
find what an include costs, run `accumulated-persistence` on the slow form
(chapter `humans/01-logic-and-prover.md` section 1.7.1).
