# 12. Costs the step count does not see: tau, arithmetic-5, and a rule that crashed SBCL

## The wound

Three costs fn measured that neither the prover-step ratchet nor the frame
profile reports.

- **The tau system.** A book whose forms take tenths of a second for a few
  thousand steps each "is the **tau system** or a library's
  `syntaxp`/`bind-free` tests, neither of which counts as prover steps or
  shows as frames, so neither `proof_profile.py` nor `rule_cost.py` can name
  it". Turning tau off after the includes "halved the proof time of
  `served-catalog`, `catalog` and `heap-reservation` at unchanged steps"
  (2026-09-28). Tree-wide it is not uniformly waste: "of 1,445 books, tau off
  cost 1,400 s more than it saved in total (bp-node-foundation 2 s to 33 s,
  replay-identity-index 2 s to 45 s); 183 books saved a second or a fifth, and
  109 of those still did when measured again on both boxes"
  [fn: docs/proof-style.md:621-644 @3bbfc4dca].
- **arithmetic-5.** In `heap-reservation`, "a 30,000-step theorem took 1.1 s
  with them enabled and 0.4 s without" [fn: docs/proof-style.md:645-648 @3bbfc4dca];
  for base64, "arithmetic-5 was about 10 times slower than a few
  fixed-modulus lemmas (lane shared-books)"
  [fn: docs/proof-style.md:912 @3bbfc4dca].
- **A rule that crashed the Lisp.** "A `:linear` rule with `:trigger-terms`
  and a `:rewrite` class on the same conclusion crashed SBCL with a memory
  fault (lane shared-books, 2026-09-28)" [fn: docs/proof-style.md:911 @3bbfc4dca].

## What was done about it

- Tau off book by book where the saving was confirmed: each such book keeps
  `(local (in-theory (disable (tau-system))))` after its includes and enables
  it in the one form that was shorter with it; `tools/tau_cost.py` measures
  every book twice side by side and `apply` writes the disable; the default
  stays on [fn: docs/proof-style.md:627-644 @3bbfc4dca].
- `heap-reservation` "names `arithmetic-5`'s rules as one local theory and
  closes them past the definitions that need them"
  [fn: docs/proof-style.md:645-647 @3bbfc4dca]; fixed moduli get small lemmas
  instead [fn: docs/proof-style.md:912 @3bbfc4dca].
- The crashing rule was split "into a type rule and a plain `:linear` rule"
  [fn: docs/proof-style.md:911 @3bbfc4dca].

## The lesson

Measure wall time beside steps, because ACL2 counts as a step only "each call
of the system functions `rewrite` and `expand-abbreviations`"
[:doc set-prover-step-limit]; work in tau and in `syntaxp`/`bind-free`
predicates is real time with no step. The tau system is switched by one rune,
`(:EXECUTABLE-COUNTERPART TAU-SYSTEM)` [:doc tau-system], so its cost is
measurable per book: turn it off where a side-by-side measurement shows a
saving, not by default. Include a large arithmetic library locally and close
its rules where they stop being needed (chapter
`humans/02-rewriting-theories-books.md` section 2.8.6 quotes the community's
"Avoid any non-local inclusion of arithmetic libraries"). Give a theorem one
rule class per job: a `:linear` rule with explicit trigger terms is its own
rule [:doc linear], and fn's crash came from combining it with `:rewrite` on
the same conclusion.

## The shape to copy

The book-local tau switch after the includes, and for a form that fails or
slows without tau, the local enable/disable pair that fn's `tau_cost.py
apply` writes around it [fn: docs/proof-style.md:630-637 @3bbfc4dca]:

```lisp
(local (in-theory (disable (tau-system))))   ; after the book's includes

(local (in-theory (enable (tau-system))))    ; around the one form that needs it
(defthm ...)
(local (in-theory (disable (tau-system))))
```

and the measurement that justifies it: the book's forms loaded twice, as is
and with tau off after its includes, on a quiet box, comparing total time at
unchanged steps [fn: docs/proof-style.md:625-639 @3bbfc4dca].
