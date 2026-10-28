# 14. `git log` read as green for a day, and other greens that were not

## The wound

"on 2026-09-21 `dev` had been red for a day in `books/stx-evidence-records`,
`books/checkpoint-compaction`, `books/hybrid-store` and `books/feed-connection`,
each committed by a lane that never certified it, with the failures already
recorded at those digests in the archive while every reader took `git log`
for certification" [fn: docs/proofs.md:449-453 @3bbfc4dca]; the review's
finding F4 puts it as "five commits changed the machine under invariant books
nobody recertified, and `git log` read as green for a day"
[fn: docs/proofs.md:466-469 @3bbfc4dca].

The same misreading came in three other forms.

- **Exit codes.** "the certify driver ends in `(quit)`, which ACL2 reaches
  whether or not the inner `ld` returned on a failed `certify-book`, so a book
  that failed still exits 0. On `dev-909e055` the exit codes name one failing
  root and `book_results` names twenty-five" [fn: docs/proofs.md:607-611 @3bbfc4dca].
  This guide's own first draft of an example failed its guard proof and the
  log still ended "Exit code from ACL2 is 0", followed by cert.pl's
  "carried-recognizer.cert seems to be missing" and "CERTIFICATION FAILED"
  [measured: examples/certify.sh fn-lessons/carried-recognizer.lisp on the
  draft whose ids-okp guard was too weak, 2026-10-28, laptop ACL2 8.7].
- **Scenario harnesses.** Every scenario assertion "appended a sentence to a
  `gaps` list, the exit read only `Step.failed`", so the two-node gate could
  watch an article fail to arrive and exit 0: "the headline "63 steps, 0
  failed" structurally could not include a violated scenario assertion"
  [fn: docs/proofs.md:738-746 @3bbfc4dca].
- **A gate over a subset.** "Two reds born in train 63's heap probe ...
  surfaced at trains 71 and 73, 5.6 h and 7.5 h later. Train 63's image gate
  ended "done status 0" over a subset of modules"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:56 @worktree].

At the freeze, `green_check --strict` reported "1,354 of 3,062 certificates
stale at their closure key" [fn: build/coordinator/ANATOMY-20261009.md:63 @worktree].

## What was done about it

- `tools/green_check.py` hashes every root and its include closure and finds
  the newest run "that recorded a verdict for those exact bytes, so each book
  is green at its current digest, *red* at its current digest, never at this
  digest (naming its last green at an older one), or never a requested root
  anywhere"; `--strict` fails on a red at current bytes
  [fn: docs/proofs.md:442-454 @3bbfc4dca].
- The same audit is the merge gate: `green_check.py --changed-since REV
  --strict` "lists the books and test books whose bytes differ from the merge
  base with `REV`, every audited book whose include closure reaches one, and
  each one's verdict at the bytes a merge would carry; it exits 1 unless every
  row is green" [fn: docs/proofs.md:462-466 @3bbfc4dca].
- Per-root rows come "from the manifest's `book_results`, not from
  `acl2_exit_codes`" [fn: docs/proofs.md:607-608 @3bbfc4dca].
- Harness verdicts got their own vocabulary (`held`, `violated`,
  `inconclusive`, `not-exercised`, `not-built`, `limitation`), a declared
  inventory "so an assertion the run never reached is emitted rather than
  lost", and a hash over the records "so a verdict cannot be typed in
  afterwards" [fn: docs/proofs.md:748-767 @3bbfc4dca].
- "An owned red is a red; it never shares a green with "satisfied""
  [fn: build/coordinator/RULINGS.md:20 @worktree].

## The lesson

The only evidence that a book certified is a certificate made from its
current bytes and its current closure's bytes; a commit message, an exit
code, a log line and a passing sibling are not. `certify-book` "writes a
certificate recording not only that the book was certified but also ... a
book-hash for each of the books involved" [:doc certify-book], and cert.pl
judges a run by that file, which is why a missing `.cert` was its verdict when
ACL2 itself exited 0 (above). A gate states which subjects it decided; a subject it
did not reach is reported as not reached, never folded into a pass.

## The shape to copy

The merge gate, verbatim [fn: docs/proofs.md:462-466 @3bbfc4dca]:

    python3 tools/green_check.py --changed-since REV --strict

In any ACL2 project the same question without fn's tool is: for each book
whose bytes or whose closure's bytes changed since REV, is there a `.cert`
made from exactly those bytes? `cert.pl` answers it for a set of targets in
one run (chapter `humans/02-rewriting-theories-books.md` section 2.10.5),
judging success by the `.cert` it finds, not the exit code it is given
[measured: the cert.pl log quoted above].
