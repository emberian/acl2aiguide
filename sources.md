# Sources

Every reference cited anywhere in this guide, grouped by kind. A chapter lane
reports the sources it added; the coordinator keeps this file whole.

## Toolchain (what the examples certify with)

- ACL2 8.7 (github tag 8.7, sha256 `d6013c22...` of the tarball), built on
  SBCL 2.6.8 by `~/dev/fn/tools/build_local_acl2.sh` into `~/tools/acl2-fn/`.
  Launcher: `~/tools/acl2-fn/acl2-literal-4g-tls64k` (`--tls-limit 65536
  --dynamic-space-size 4096 --control-stack-size 64`).
- Community books: `~/tools/acl2-fn/acl2-8.7/books`. The manual's source is
  `books/system/doc/acl2-doc.lisp` (one `(defxdoc TOPIC ...)` per topic);
  community-book topics are `defxdoc` forms in the books themselves
  (`centaur/fgl/doc.lisp`, `kestrel/c/atc/doc.lisp`, `kestrel/apt/doc.lisp`,
  `doc/practices.lisp` for `best-practices`).
- `cert.pl`: `books/build/cert.pl` (`:doc build::cert.pl`).
- Community books **certified on the laptop** (an example may include only
  these, or a book whose closure certifies in under two minutes):
  `arithmetic/top`, `arithmetic/top-with-meta`, `arithmetic-5/top`,
  `ihs/quotient-remainder-lemmas` (and the ihs books under it),
  `std/lists/*` (42 books: append, len, nth, nthcdr, rev, revappend, take,
  update-nth, ...), `std/testing/{assert-bang,assert-equal,must-fail,
  must-eval-to,must-eval-to-t}`, `std/util/{bstar,define,defines,defrule,
  deflist,defaggregate,defval,...}`, `std/basic/*`, `tools/{flag,
  def-functional-instance,rulesets,match-tree,easy-simplify,templates,...}`,
  `misc/{definline,expander,total-order,...}`, `xdoc/*`.
  NOT certified here (cite their own tests instead of certifying): `demos/*`,
  `std/stobjs/*`, `centaur/fgl`, `centaur/gl`, `centaur/fty` (4 of 21),
  `kestrel/apt`, `kestrel/c/atc`, `centaur/bitops` (6 of 71).

## ACL2 manual topics (`:doc TOPIC`)

Cited by `humans/01` and `humans/02`: accumulated-persistence, acl2-count,
apply$, architecture-of-the-prover, assert-event, backchain-limit,
best-practices, bind-free, book-hash, books, break-rewrite, case-split,
case-split-limitations, certify-book, checkpoint-summary-limit,
clause-processor, comp, compound-recognizer, computed-hints, congruence,
conventional-normal-forms, current-theory, cw-gstack, defattach, defaxiom,
define-trusted-clause-processor, definition, defpkg, deftheory,
deftheory-static, defthmd, defttag, defun, defun-mode, defun-mode-caveat,
disable, dmr, e/d, elim, enable, encapsulate, equivalence,
executable-counterpart, file-extensions, force, forward-chaining,
free-variables, frequently-asked-questions-by-newcomers,
functional-instantiation-example, generalizing-key-checkpoints,
gentle-introduction-to-ACL2-programming, goal-spec, ground-zero, hide, hints,
hints-and-the-waterfall, in-theory, include-book, induction,
induction-coarse-v-fine-grained, induction-heuristics,
introduction-to-key-checkpoints, introduction-to-the-theorem-prover,
lemma-instance, linear, local, local-incompatibility, logic,
logic-knowledge-taken-for-granted-inductive-proof, loop-stopper, make-event,
meta, minimal-theory, monitor, mutual-recursion, non-linear-arithmetic, o-p,
ordinals, otf-flg, pbt, pe, pl, portcullis, post-induction-key-checkpoints,
pr, program, provisional-certification, pso, pstack, r-and-i-data-types,
refinement, rewrite, rewrite-stack-limit, rule-classes, rulers, rune,
set-default-hints, set-enforce-redundancy, set-gag-mode,
set-match-free-default, set-non-linearp, set-prover-step-limit, simple,
skip-proofs, splitter, summary, syntaxp, tau-system, the-method, theories,
theory-invariant, theory-management, type-prescription, type-reasoning, ubt,
using-enabled-rules, with-prover-step-limit, with-prover-time-limit,
working-with-packages, xargs, |About Types|, |Common Lisp|.

## Community books (`books/PATH`)

- `build/doc.lisp` (cert.pl: lines 34, 297, 558), `doc/practices.lisp:511`
  (rule naming), `std/testing/must-fail.lisp:17`,
  `std/testing/must-succeed.lisp:17`, `tools/flag.lisp:93` (humans/01, 02).

## fn books and documents (`PATH @SHA`, sha of `origin/dev` unless stated)

- `origin/dev` = `3bbfc4dcad5daa709ef57885a905fddd4b351361` (2026-10-27).
- `docs/proof-style.md`, `docs/proofs.md`, `docs/engineering.md`,
  `docs/implementation.md`, `docs/resource-contract.md`.
- `books/store-log.lisp:368`, `books/store-log-stream.lisp:335` (the
  load-bearing rule pair, humans/02).
- `build/coordinator/ANATOMY-20261009.md`, `PROCESS-AUDIT-20261009.md`,
  `AUDIT-TWO-WEEKS-20261013.md`, `EMBER.md`, `RULINGS.md`,
  `CUT-M2-PLAN-20261027.md`, `lanedumps/cut-m2a-lb-continuation.md`,
  `REPRESENTATION-HISTORY-20261028.md`.

## Papers (`~/paperbin/FILENAME`)

(filled as chapters land)

## Transcripts (`cv show SESSION --around INDEX`)

- `a97d40c2#529`: fn rule-hygiene lane's probe naming the `fn-lg-slice` /
  `fn-lgw-slice-is-take` loop runes (humans/02).

## Measurements

Each `[measured: ...]` in a chapter names its form; all were taken on the
laptop with ACL2 8.7 / SBCL 2.6.8 from the forms of the cited example book.
