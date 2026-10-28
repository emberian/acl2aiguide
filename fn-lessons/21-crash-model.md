# 21. The crash model: what it models, what it leaves out, and how to make it tougher

## The wound

The first model was a hypothesis dressed as a model. Crash model v2's
section 0, "Why the present model is not acceptable": `fn-sf-crash-imagep`
"is a model of *namespace observations* ... That is the right *conclusion*.
It is stated as the *hypothesis*"; "Old-or-new is assumed, not derived";
"There are no torn writes"; "`fsync` failure has no semantics"; "Directories
are prose"; and "The named assumptions are strawmen" that "no theorem
instantiates" [fn: specs/crash-model-v2.md:27-68 @3bbfc4dca].

v2 (`books/byte-store.lisp`) is a real model: inodes, directories and an
ordered list of pending operations; `fsync(fd)` drains that inode's writes,
`fsync(dirfd)` that directory's entries; "A crash keeps the durable tables and
lands an arbitrary subsequence of the pending operations, each write cut into
write-unit pieces that land, land as zeros, or land as garbage"; every
syscall takes an outcome chosen by the environment, and "a failed fsync lands
a torn selection and discards the rest (fsyncgate)"
[fn: books/byte-store.lisp:3-14 @3bbfc4dca]. Each feature is tied to a
paper [fn: specs/crash-model-v2.md:710-724 @3bbfc4dca], and it is "A
specification, by design": the host does the syscalls, and only profile,
frame and transaction-name helpers of the model execute
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:79 @worktree].

What it leaves out, it names: media corruption ("durable octets change with
no pending write ... not stated in v2"), a fence that returns `:ok` without
committing ("the boundary of A-CRASH-IMAGE"), non-POSIX namespaces, and
whole-store rollback [fn: specs/crash-model-v2.md:1967-1990 @3bbfc4dca]. Its
qualification is "process death only; no power-loss claim"
[fn: specs/crash-model-v2.md:1934-1935,2114 @3bbfc4dca]. In the definitions,
a crash rebuilds the state from the durable tables and the selected pending
operations, and a read takes no outcome at all
[fn: books/byte-store.lisp:503-508,659-661 @3bbfc4dca]. And fn's assumption
encapsulates "state the assumptions; they do not yet apply them. No theorem in
the tree takes one as a hypothesis today"
[fn: docs/proofs.md:834-836 @3bbfc4dca].

Ember, 2026-10-28: "we're not convinced that our crash model is actually an
appropriate model of the OS or hardware, and we should make sure that our
crash model is "more tough.""
[fn: build/coordinator/EMBER.md:427 @worktree]. The fn2 reading list's table
"Crash model: what ours misses, by paper" sets out 22 behaviours against v2:
durable data corrupted at rest ("absent: crash and every syscall leave
`inodes`/`dirs` untouched"), a `read` that fails ("absent: `fn-bs-read` takes
no outcome"), misdirected and lost writes, a power cut corrupting data that
was not being written, sticky device death, in-flight writes completing out of
order, concurrent syscalls at the crash, crashes during recovery, and "The
model itself never checked against real kernels"
[paper: README-fn2-20261028.md, "Crash model: what ours misses, by paper", rows 1-22].
Two of those rows checked against their papers: flying writes, "Well-formed
records end up in the wrong place"
[paper: zheng2013-ssd-robustness-under-power-fault.txt, Table 1], and
identity discrepancies whose cause "could be (i) a lost write, which
typically occurs because a write destined for disk is not written but thought
of as written, or (ii) a misdirected write", with "actual cases when the disk
firmware replied successfully to a write that was never written to stable
media" [paper: bairavasundaram2008-analysis-data-corruption-storage-stack.txt, section 2.3 "Corruption Classes"].

## What was done about it

v2 replaced the namespace-observation model, moved the trust boundary to "one
constrained function whose constraint is "the platform's crash is one the
model admits"", and transcribed the host's syscall sequences as programs over
the model [fn: specs/crash-model-v2.md:79-84 @3bbfc4dca]. Platform
qualification is designed as functional instantiation: "every theorem that
took A-DURABILITY as a hypothesis transfers to that platform by
`(:functional-instance <theorem> (fn-assume-durability-image
qual-apfs-image))`, and the transfer is checked by ACL2 rather than asserted
in prose" [fn: docs/proofs.md:821-832 @3bbfc4dca]. The fault campaign was
required to be able to fail: a test-only flag makes the host link before it
fsyncs, and the campaign must then fail; "A campaign that cannot fail on a
known-bad host is not evidence" [fn: specs/crash-model-v2.md:2086-2094 @3bbfc4dca].
Media damage stayed outside the model and was handled by ruling: "a corrupted
column page under a valid root (media damage) becomes a named read error on
first touch" [fn: build/coordinator/RULINGS.md:46 @worktree].

## The lesson

Model the environment as an adversary with an enumerated set of moves, each
move tied to evidence that real devices make it, and make every exclusion a
named assumption that some theorem actually takes as a hypothesis. A tougher
model adds moves, not cases: durable units that change with no write, reads
that fail or return another unit, fences that lie, and crashes during
recovery; theorems then claim detection where prevention is impossible. In
ACL2 the shape is an `encapsulate` whose constraint is the platform's freedom
and whose local witness shows it is satisfiable [:doc encapsulate], with each
platform discharged by `:functional-instance`, whose obligations are "the
replacement of the `fi`'s by the `gi`'s in constraints that ``support'' the
lemma" [:doc lemma-instance]. Check the model against a real system too: run
it as an oracle over recorded traces, as the reading list's row 21 proposes
[paper: README-fn2-20261028.md, row 21].

## The shape to copy

v2's own assumption form: one constrained function for the platform's crash,
over every oracle, with the qualification hook named in its comment
[fn: specs/crash-model-v2.md:1921-1944 @3bbfc4dca]:

```lisp
; A-CRASH-IMAGE.  The platform's crash, whatever it does, leaves an image the
; byte model admits.  ORACLE is the platform's freedom (power timing, drive
; cache, scheduler); the constraint is over every oracle.
(encapsulate
  (((fn-assume-physical-crash * *) => *))
  (local (defun fn-assume-physical-crash (s oracle)
           (declare (ignore oracle))
           (fn-bs-crash s nil)))                ; the lose-everything image
  (defthm fn-assume-physical-crash-is-admissible
    (implies (fn-bs-statep s)
             (fn-bs-crash-imagep s (fn-assume-physical-crash s oracle)))))
```

and the list of exclusions written next to it, each "named with the contract
a future assumption would need, so that no theorem here is read as claiming
it" [fn: specs/crash-model-v2.md:1967-1968 @3bbfc4dca]. The mechanism of
transferring a generic theorem to a concrete function is chapter
`humans/02-rewriting-theories-books.md` section 2.9.3, with
`examples/books/encapsulate-fi.lisp` [example: examples/books/encapsulate-fi.lisp].
