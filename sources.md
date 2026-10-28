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

(filled as chapters land)

## Community books (`books/PATH`)

(filled as chapters land)

## fn books and documents (`PATH @SHA`, sha of `origin/dev` unless stated)

- `origin/dev` = `3bbfc4dcad5daa709ef57885a905fddd4b351361` (2026-10-27).
- `docs/proof-style.md`, `docs/proofs.md`, `docs/engineering.md`,
  `docs/implementation.md`, `docs/resource-contract.md`.
- `build/coordinator/ANATOMY-20261009.md`, `PROCESS-AUDIT-20261009.md`,
  `AUDIT-TWO-WEEKS-20261013.md`, `EMBER.md`, `RULINGS.md`,
  `CUT-M2-PLAN-20261027.md`, `lanedumps/cut-m2a-lb-continuation.md`,
  `REPRESENTATION-HISTORY-20261028.md`.

## Papers (`~/paperbin/FILENAME`)

(filled as chapters land)

## Transcripts (`cv show SESSION --around INDEX`)

(filled as chapters land)
