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
  `kestrel/apt` (except the `propagate-iso` closure, below),
  `kestrel/c/atc`, `centaur/bitops` (6 of 71).
  Certified 2026-10-28 for `examples/transport/`: the closures of
  `kestrel/apt/propagate-iso`, `std/util/defiso`, `std/util/defmapping` and
  `std/system/theorem-namep` (about 160 books, 62 s wall at `-j 4`).

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

Cited by `humans/03` and `humans/04` (beyond the above): arrays,
attach-stobj, constraint, defabsstobj, defabsstobj-missing-events, defexec,
defstobj, defun-nx, ec-call, evaluation, fast-alists, functional-instantiation,
guard, guard-debug, guard-evaluation-table, guard-introduction, hons,
hons-and-memoization, io, mbt, memoize, nested-stobjs,
programming-with-state, set-verify-guards-eagerness, state, stobj,
stobj-attachment-restrictions, stobj-table, swap-stobjs, sys-call, the,
unmemoize, unsigned-byte-p, verify-guards, with-local-stobj.

Cited by `ai/00`..`ai/02` (beyond the above): acl2-doc, args,
book-hash-mismatch, doc, embedded-event-form, ld-error-action,
ld-pre-eval-print, pc, set-inhibit-output-lst, uncertified-books,
with-guard-checking-event.

Cited by `ai/03`..`ai/06` (beyond the humans chapters they condense):
acl2-customization, ld-redefinition-action, set-match-free-error.

Cited by `fn-lessons/` (beyond the above): defmacro, ld,
ld-redefinition-action, loop$, table, top-level, verify-termination.

Cited by `humans/05` and `humans/06` (beyond the above): assert$, declare,
defstobj, defstobj-element-type, defun-inline, efficiency, evaluation,
guards-and-evaluation, hons-summary, mbt, note-6-2, profile, the, time$,
with-local-stobj.

## Community books (`books/PATH`)

- `build/doc.lisp` (cert.pl: lines 34, 297, 558), `doc/practices.lisp:511`
  (rule naming), `std/testing/must-fail.lisp:17`,
  `std/testing/must-succeed.lisp:17`, `tools/flag.lisp:93` (humans/01, 02).
- humans/03, 04: `centaur/bitops/top.lisp:53-80`,
  `centaur/fgl/def-fgl-thm.lisp:108-120`, `centaur/fgl/doc.lisp` (35-91),
  `centaur/fgl/tests.lisp:375-378`, `centaur/gl/doc.lisp:38-70`,
  `centaur/gl/tutorial.lisp:377-400`, `defexec/`,
  `demos/attach-stobj/mem_ht.lisp:73-81`,
  `demos/defabsstobj-example-2.lisp:314-321`,
  `demos/defabsstobj-example-3.lisp:5-12`, `ihs/basic-definitions.lisp:394-433`,
  `ihs/ihs-doc-topic.lisp`, `std/io/base.lisp:956-993`,
  `std/io/file-measure.lisp`, `std/util/defaggregate.lisp:47-55`,
  `std/util/define.lisp` (71-92, 216-220), `std/util/returnspecs.lisp:36-46`,
  `tools/def-functional-instance.lisp:34-56`.
- `build/doc.lisp:673` (the default certify command), `std/testing/must-fail.lisp:17`
  (ai/00..02).
- `kestrel/c/atc/doc.lisp` (316-320, 328, 375-420, 1536-1617),
  `kestrel/c/atc/tutorial.lisp`, `kestrel/c/atc/tests/{checksum,loops}.lisp`,
  `tests/checksum-test.c`, `tests/compile.sh`; `kestrel/apt/doc.lisp:68-85`,
  `isodata-doc.lisp`, `expdata-doc.lisp`, `parteval-doc.lisp`,
  `finite-difference.lisp`, `casesplit-doc.lisp`, `lift-iso-doc.lisp`,
  `tailrec-doc.lisp` (humans/05).

## fn books and documents (`PATH @SHA`, sha of `origin/dev` unless stated)

- `origin/dev` = `3bbfc4dcad5daa709ef57885a905fddd4b351361` (2026-10-27).
- `docs/proof-style.md`, `docs/proofs.md`, `docs/engineering.md`,
  `docs/implementation.md`, `docs/resource-contract.md`.
- `books/store-log.lisp:368`, `books/store-log-stream.lisp:335` (the
  load-bearing rule pair, humans/02).
- humans/03, 04: `specs/crash-model-v2.md` (29-68, 617-731, 1176-1186,
  1934-1935, 1967-1990, 1997), `books/byte-store.lisp` (1-14, 384-387,
  421-433, 449-475, 487-492, 510-517, 557-563, 609-615, 663-667),
  `books/assumptions.lisp` (14-16, 23-26, 56-97),
  `books/owner-checkpoint-open.lisp` (4-12, 73-121, 134-149),
  `books/def-carried.lisp` (23-25, 39-46, 175-207), `books/catalog.lisp`
  (14-17, 50-115), `books/catalog-logic.lisp` (4-18, 2372),
  `books/catalog-paged.lisp` (37-50, 76-79, 116-144),
  `books/history-columns.lisp:13-31`, `books/octets-stobj.lisp` (72-79,
  1167-1170), `books/def-representation.lisp:13-28`,
  `books/proto/adt.lisp:266-273`, `books/def-loop.lisp` (5-20, 60-66,
  124-127, 830-850), `books/defkeystone.lisp` (13-42, 48-51, 124-133,
  148-150), `books/runtime-contract.lisp` (1-15, 62-65, 89-91, 98-111),
  `OWED.md:11-21`; `@worktree`: `STRATEGY-20261006.md` (266-267).
- ai/06: `docs/proofs.md` (636-645), `@worktree` `EMBER.md:392`,
  `lanedumps/cut-m2a-lb-continuation.md:22`.
- fn-lessons/: `host/native/io.lisp:264-265`, `tools/list_codec_baseline.json`,
  `books/catalog.lisp:2038,4633 @4e56f2d01` (the hand-written obligation
  block of 2026-10-01), `books/def-loop.lisp:170-172`,
  `books/runtime-contract.lisp:3-34`, `specs/crash-model-v2.md` (27-84,
  710-724, 1921-1990, 2086-2094, 2114); `@worktree`:
  `scholar-proof-engineering-2026-10-01.md` (the 285 obligations / 5,800
  lines figure and the def-loop counts).
- humans/05, 06: `AGENTS.md` (20-37), `OWED.md` (3-21),
  `specs/storage.md` (443-457, 563-572, 1786-1791), `books/msgid-linear-exec.lisp`
  (7-36, 146-153, 244-263), `books/store-log.lisp` (9-13, 52-53, 102-108),
  `books/owner-log-route.lisp:18-25`, `books/owner-commit-pipeline.lisp:1-22`,
  `books/runtime-contract.lisp:12-111`, `books/def-loop.lisp` (5-128),
  `books/def-representation.lisp` (6-78), `books/definterface.lisp:3-41`,
  `books/defkeystone.lisp:48-63`, `books/protocol-table.lisp` (4-80, 300-302,
  395-415), `host/native/owner.lisp:549-553`, `tools/certify_books.py:108`,
  `tools/proof_repl.py:4-10`, commit `9d5a3f99b` (the checker deletions).
- `@worktree` (untracked coordinator documents, read 2026-10-28):
  `ANATOMY-20261009.md`, `AUDIT-TWO-WEEKS-20261013.md`,
  `PROCESS-AUDIT-20261009.md`, `REPRESENTATION-HISTORY-20261028.md`,
  `EMBER.md`, `RUNTIME-MODEL-DRAFT-20261009.md`, `CUT-M2-PLAN-20261027.md`,
  `RULINGS.md`, `lanedumps/cut-m2a-lb-continuation.md`,
  `lanedumps/actors.md`, `lanedumps/extract-forms.md`.
- `~/dev/minidregg/CLAUDE.md:18-21` (the statement-first law).
- `build/coordinator/ANATOMY-20261009.md`, `PROCESS-AUDIT-20261009.md`,
  `AUDIT-TWO-WEEKS-20261013.md`, `EMBER.md`, `RULINGS.md`,
  `CUT-M2-PLAN-20261027.md`, `lanedumps/cut-m2a-lb-continuation.md`,
  `REPRESENTATION-HISTORY-20261028.md`.

## Papers (`~/paperbin/FILENAME`)

- humans/03, 04: `goel2013-acl2-abstract-stobjs-isa-modeling.txt`,
  `kaufmann2025-acl2-mutable-objects-several-implementations.txt`,
  `swords2011-acl2-bit-blasting-gl.txt`, `swords2015-acl2-fix-your-types.txt`,
  `pillai2014-all-file-systems-not-created-equal.txt`,
  `rebello2020-can-applications-recover-fsync-failures.txt`,
  `zheng2013-ssd-robustness-under-power-fault.txt`,
  `chen2015-fscq-crash-hoare-logic.txt`,
  `chen2017-dfscq-verifying-high-performance-crash-safe-fs.txt`,
  `sigurbjarnarson2016-yggdrasil-push-button-crash-refinement.txt`,
  `chajed2019-perennial-crash-safety-concurrency.txt`,
  `mohan2018-crashmonkey-bounded-black-box-crash-testing.txt`.
- fn-lessons/: `bairavasundaram2008-analysis-data-corruption-storage-stack.txt`
  (section 2.3), `README-fn2-20261028.md` (the fn2 reading list's "Crash
  model: what ours misses, by paper" table, rows 1-22).
- `tigerbeetle2026-tiger-style.md` ("Safety"; byte-identical to TigerBeetle's
  `docs/TIGER_STYLE.md` fetched 2026-10-28), `tigerbeetle2026-architecture.md`
  ("Single Thread", "Static Memory Allocation"),
  `tigerbeetle2026-concepts-performance.md` ("Batching, Batching, Batching"),
  `tigerbeetle2026-internals-vopr.md` (lines 29-40, 50-54) (humans/05).
- `coglio2022-acl2-atc-proof-generating-c-code-generator.txt` (abstract,
  section 1), `coglio2020-acl2-apt-isomorphic-data-type-transformations.txt`
  (humans/05).

## Transcripts (`cv show SESSION --around INDEX`)

- `a97d40c2#529`: fn rule-hygiene lane's probe naming the `fn-lg-slice` /
  `fn-lgw-slice-is-take` loop runes (humans/02).
- `a5779663#0`: a lane brief relaying the paged catalog's memory measurement
  and its 35 obligations (humans/03).
- `ac5fb887#20`: `with-local-stobj` of an attachable stobj in compiled code
  making certification illegal (humans/03).
- ai/00..02: 118 transcript citations, listed in place in the chapters
  (sessions `01a0b43d`, `01a0c2bc`, `01a0f057`, `01a0f3b3`, `01a11dcf`,
  `01a1311e`, `01a132b1`, `01a1331b`, `01a13b1a`, `01a13b94`, `8d4521d3`,
  `b3f4abb5`, and 60 `agent-*` sub-agent transcripts); each was checked
  against the transcript text by the lane that cited it.
- fn-lessons/: `35f3668a#1311`, `#1377`, `#1466`; `905fe751#2886`, `#4541`;
  `9627d694#2912`; `adb603dc#976`; `be1e9dcf#883`, `#2198`, `#4275`, `#6393`
  (ember's words, as EMBER.md cites them); `ad44eec2#263` (the false OB-2).
- `b54b6026#1061`: the minidregg (Lean) statement approved on polarity alone
  and refuted by its satisfiable witness (humans/06).

## Measurements

- The `:linear` memory fault (humans/02 2.6.3, ai/00 pitfall 6): a `:linear`
  rule with `:trigger-terms` and a non-inequality conclusion, admitted, faults
  SBCL at first use (laptop, ACL2 8.7 / SBCL 2.6.8, 2026-10-28).
- The book-hash question (humans/05 5.9): a comment-only edit to a certified
  book includes with no warning under `ACL2_BOOK_HASH_ALISTP=NIL`; a body edit
  is refused with a book-hash mismatch (laptop, ACL2 8.7, 2026-10-28).

Each `[measured: ...]` in a chapter names its form; all were taken on the
laptop with ACL2 8.7 / SBCL 2.6.8 from the forms of the cited example book.
