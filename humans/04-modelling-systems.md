# 4. Modelling systems

Chapter 3 was about data. This chapter is about systems: programs that
talk to an operating system, keep state across crashes, step through
events, refine a simple specification into an efficient implementation,
and are built from generic layers. It ends with what makes any of their
theorems worth having: teeth.

The fn project is the worked example throughout. It is an NNTP server
whose books were meant to be the program the host runs, and its documents
say what that took. Citations follow chapter 3's conventions: `[:doc X]`
for the ACL2 8.7 manual, `[books: P]` for community books, `[fn: P:L
@3bbfc4dca]` for fn at `origin/dev` (files under `build/coordinator/` are
untracked and cited `@worktree 2026-10-28`), `[paper: F]` for
`~/paperbin`, `[cv: S#I]` for a transcript message, `[example: P]` for a
certified book of this guide, and `[measured: ...]` for REPL runs on the
laptop (ACL2 8.7, SBCL 2.6.8, 2026-10-28).

The examples cited here:

| book | what it shows |
| --- | --- |
| `examples/systems/state-io.lisp` | I/O through the ACL2 state, and what it costs to prove anything about it |
| `examples/systems/crash-store.lisp` | a crash model: pending writes, fences, torn crashes, a two-fsync commit theorem and its teeth |
| `examples/systems/assumption-instance.lisp` | a named platform assumption discharged by functional instance |
| `examples/systems/step-invariant.lisp` | a step function with typed outcomes, trace induction and teeth |
| `examples/systems/closed-recognizer.lisp` | a transition keystone proved with the recognizer closed |
| `examples/systems/refinement.lisp` | recovery from a checkpoint equals full replay, and its encoded rung |
| `examples/systems/generic-fold.lisp` | an encapsulated monoid, a generic theorem, two functional instances |
| `examples/systems/generic-loop.lisp` | a loop-twin bridge proved once and instantiated with no induction |

## 4.1 I/O and the operating system

### What goes wrong

**`sys-call` is outside the logic, and the logic knows it.** "This function
logically returns `nil`. However, it makes the indicated call to the host
operating system ... (not during a proof) ... This is an advanced feature
that requires a trust tag" [:doc sys-call]. During a proof it does
nothing: "Sys-call does not invoke the operating system when it is invoked
inside the theorem prover or proof-builder ... presumably we only want to
reason about the return value, not write a file during a proof!"
[:doc sys-call]. So no theorem can say anything about what a `sys-call`
did. The manual's warning about its power is concrete: Bob Boyer's example
uses it to attach `gdb` to the running Lisp and change `*features*`
[:doc sys-call].

**A trust tag is a contract you cannot check.** "A trust tag thus
represents a contract: The writer of such a book is guaranteeing that the
book extends ACL2 in a 'correct' way as defined by the writer of the book"
[:doc defttag]; a book that uses one is certified with `:ttags` and
included with `:ttags`, and "a book's certificate contains a list of ttags
that are active in that book, or in a book that is included (possibly
locally)" [:doc defttag]. fn's rule: "Do not turn `skip-proofs`, trust
tags, or axioms into a certification shortcut", and "A certified book can
still depend on trusted facilities; disclose those explicitly"
[fn: docs/proofs.md:90-94 @3bbfc4dca].

**I/O inside the logic is possible, and proving anything about it needs a
library.** ACL2 does have channels: "In ACL2, input and output are to or
from objects called 'channels,' which are actually symbols", typed
`:character`, `:byte` or `:object` [:doc io], and "Logically speaking, a
state object is a true list" of fields that include open input and output
channels, readable and written files and a file clock [:doc state]. The
example writes a byte list to an open `:byte` channel in a guard-verified
loop, and reads a bounded number of bytes back; at the REPL
`(save-bytes "x.bin" '(1 2 255) state)` then `(load-bytes "x.bin" 100
state)` returned `((1 2 255) <state>)` [example: examples/systems/state-io.lisp]
[measured: those two forms]. But a theorem as small as "writing bytes keeps
the state a state" did not close: the state recognizers open into the
channel tables, and restating the community library's lemma
`state-p1-of-write-byte$` with its own hint stopped at `(OPEN-CHANNEL-LISTP
(ADD-PAIR CHANNEL ...))` [measured: the lemma at the end of
`examples/systems/state-io.lisp`'s drafts]. The lemmas live in
`std/io/base.lisp` (`state-p1-of-write-byte$`,
`open-output-channel-p1-of-write-byte$`, with local lemmas under them)
[books: std/io/base.lisp:956-993], which is not certified on this laptop.
A read loop over a channel needs a measure on the channel's contents,
`file-measure`, from the same library [books: std/io/file-measure.lisp]; the
example bounds its loop by a count instead.

### The mechanism

The manual's map for programs that traffic in state:
"there are situations that call for reading or modifying the system state,
such as performing input and output, signaling errors, saving information
from one computation for use in a later one, or reading and updating
system-level or environmental data" [:doc programming-with-state]. State is
declared like any stobj (`(declare (xargs :stobjs state))`) or allowed by
`(set-state-ok t)`; error triples `(mv erp val state)` carry soft errors;
`sys-call`, `sys-call+` and `sys-call*` run host commands, and
`getenv$`/`setenv$` read and write the environment
[:doc programming-with-state]. The io functions are listed with their
signatures in [:doc io], for example `(open-output-channel (file-name
io-type state) (mv channel state))` and `(write-byte$ (byte channel state)
state)`.

### What fn did instead

fn's position is that the host performs effects and the books decide them,
with the operating system modelled in the logic. Its proof strategy says:
"The program used by the host must be these definitions or a justified
refinement. An abstract model plus an independently written server is
insufficient evidence for claims about the running server"
[fn: docs/proofs.md:59-61 @3bbfc4dca]. Two books carry the idea.

The **runtime contract** turns effects into data. "Every effect an
instance wants is an ACTION (kind id incarnation op args) handed to an I/O
worker; the worker's answer is a COMPLETION (kind id incarnation op
outcome), the only kind of event this layer consumes ... An instance
learns that an effect happened only from its completion; submission
establishes nothing" [fn: books/runtime-contract.lisp:1-10 @3bbfc4dca].
The layer is "written once over a constrained instance machine
(`fn-rtc-m-step`), so its theorems hold for every machine that meets the
constraint; an executable instance obtains them by `:functional-instance`"
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca]. It does not trust the
host's discipline: "A completion that matches no outstanding use -- a
duplicate, a forgery, a late completion of an earlier operation with the
same kind on the same instance, one naming a retired incarnation --
changes nothing and emits nothing (T6). The layer checks the host's
discipline; it does not assume it" [fn: books/runtime-contract.lisp:62-65 @3bbfc4dca].
And durability has one entry: "`:commit` is not an action kind. An
instance's commit observer (`fn-rtc-m-committedp`) may turn true only on
the delivery of a (:fsync (:done n)) completion of the instance's own
outstanding :fsync" [fn: books/runtime-contract.lisp:108-111 @3bbfc4dca].

The **byte store** models the file system the completions come from
(section 4.2). Every syscall in it takes its outcome from the environment
as an argument, so the theorems quantify over what the platform may
answer.

## 4.2 Crash models

### What goes wrong

The common failure is to assume the conclusion. fn's own first storage
model did: "a crash image is a frontier value that is the stable one or the
candidate, and a record list that is the stable one or the stable one plus
the exact candidate. That is the right *conclusion*. It is stated as the
*hypothesis*" [fn: specs/crash-model-v2.md:29-35 @3bbfc4dca]. The same
review lists what that model could not say: no torn writes; "`fsync`
failure has no semantics", although "on Linux, a failed `fsync` discards
the dirty pages, a retry succeeds without writing them, and reading the
file back shows the data that was never written"; directories only in
prose; and named assumptions that were "strawmen" because no theorem
instantiated them [fn: specs/crash-model-v2.md:42-68 @3bbfc4dca].

The second failure is to prove a durability property of a program that
omits a fence and not notice, because the theorem's hypotheses rule out
the case. The example's mutation section shows the concrete crash that
breaks the one-fsync commit (below).

### fn's model

The byte store, in its own header: "A store is a table of inodes (octet
lists), a table of directories (name maps), and an ordered list of PENDING
operations the process has issued and no fence has drained: byte writes to
inodes and entry updates to directories. The process observes the VIEW
(durable tables with every pending operation applied). fsync(fd) drains
exactly that inode's pending writes; fsync(dirfd) drains exactly that
directory's pending entry operations. A crash keeps the durable tables and
lands an arbitrary subsequence of the pending operations, each write cut
into write-unit pieces that land, land as zeros, or land as garbage;
afterwards nothing is pending. Every syscall takes an OUTCOME chosen by the
environment so that EIO/ENOSPC with partial progress are explicit
transitions, and a failed fsync lands a torn selection and discards the
rest (fsyncgate)" [fn: books/byte-store.lisp:1-14 @3bbfc4dca].

The parts, each a definition:

- What one write unit became: `:old` (untouched), `:new`, `:zero` ("the
  unit was allocated but its data did not land (ext4 delayed allocation,
  Ts'o 2009: zero-filled and zero-length files after a crash)"), or
  `(:garble . octs)` ("SSD shorn/torn writes, Zheng et al. FAST 2013")
  [fn: books/byte-store.lisp:421-433 @3bbfc4dca].
- The crash: the pending list with one choice per operation, applied in
  issue order. "Issue order among the survivors is what the page cache
  guarantees for one file: a later write to the same unit is never undone
  by an earlier one landing after it. Across files and directories there is
  no order at all, which subset selection already expresses"
  [fn: books/byte-store.lisp:487-492 @3bbfc4dca].
- Admissible images as a `defun-sk`, so that "every theorem about crash
  images quantifies over this predicate, never over a choice"
  [fn: books/byte-store.lisp:510-517 @3bbfc4dca].
- Fences: "fsync(fd) drains exactly the pending writes of that inode. It
  does not drain the directory entry that names the inode (ALICE, Pillai et
  al. 2014; Ferrite, Bornholt et al. 2016: 'fsync of a file does not
  persist its directory entry'), and it does not drain any other inode's
  writes" [fn: books/byte-store.lisp:384-387 @3bbfc4dca].
- The failed fence: "(errno . choices) reports failure after landing the
  torn selection CHOICES of those writes and DISCARDING the rest: the
  platform has marked the dirty pages clean (Linux ext4/xfs, Rebello et al.
  2020; PostgreSQL fsyncgate, 2018), so nothing remains for a retry to write
  and a later fsync that returns :ok fences nothing"
  [fn: books/byte-store.lisp:557-563 @3bbfc4dca].
- Rename as two operations: "the destination entry is replaced by ONE
  :set-entry, so it is old or new and never half; the source entry's
  removal is a SEPARATE pending operation on the source directory. The two
  are not assumed to land together (Pillai et al. 2014 Table 1: rename
  atomicity across a crash is per-filesystem)"
  [fn: books/byte-store.lisp:609-615 @3bbfc4dca].
- And one thing left unspecified on purpose: "the view of an inode after a
  FAILED fsync (Linux keeps the never-written data in cache and reports it
  to read, so the view and the durable content diverge). v2 adds no cache
  field; byte-store-programs requires instead that no program reads a file
  whose fence failed" [fn: books/byte-store.lisp:663-667 @3bbfc4dca].

The contracts are theorems about this model, not assumptions: a fenced
inode's durable content survives every admissible crash
(`fn-bs-crash-keeps-fenced-content`); "a crash invents nothing"; a torn
write to one inode changes no other inode; an entry after a crash "is its
durable value or the target of one of its pending operations; never a
third thing and never a partial name"; fences "drain exactly their named
set"; "the view is a fixed point of fencing and crash-with-everything-applied";
and "fsyncgate: after a failed fence, a later successful fence of the same
inode changes nothing durable" [fn: specs/crash-model-v2.md:617-708 @3bbfc4dca].
Each model feature is tied to a finding in the literature, in a table
whose rows cite Pillai et al. 2014, Bornholt et al. 2016, Chidambaram et
al. 2013, Mohan et al. 2018, Zheng et al. 2013 and 2014, Rebello et al.
2020, the SQLite powersafe-overwrite contract and Yang, Sar and Engler's
EXPLODE and FiSC [fn: specs/crash-model-v2.md:710-731 @3bbfc4dca]. The
model deliberately encodes no filesystem heuristic, "because a program that
is correct only under a heuristic is not correct (Pillai et al. 2014 section 5
'masking')" [fn: specs/crash-model-v2.md:725-728 @3bbfc4dca].

### A model small enough to read

The example keeps fn's shape at the size of one file of blocks
[example: examples/systems/crash-store.lisp]:

```lisp
(defun st (durable pending) (list durable pending))

(defun apply-writes (blocks ws)
  (if (atom ws)
      blocks
    (apply-writes (update-nth (nfix (car (car ws))) (cdr (car ws)) blocks)
                  (cdr ws))))

(defun view (s) (apply-writes (st-durable s) (st-pending s)))
(defun bwrite (i v s)
  (st (st-durable s) (append (st-pending s) (list (cons i v)))))
(defun fsync-ok (s) (st (view s) nil))

; one choice per pending write: :drop, :new, :zero, or (:garble . value)
(defun land (ws choices)
  (if (atom ws)
      nil
    (let ((w (car ws)) (c (if (consp choices) (car choices) :drop)))
      (cond ((eq c :new) (cons w (land (cdr ws) (cdr choices))))
            ((eq c :zero) (cons (cons (car w) 0) (land (cdr ws) (cdr choices))))
            ((and (consp c) (eq (car c) :garble))
             (cons (cons (car w) (cdr c)) (land (cdr ws) (cdr choices))))
            (t (land (cdr ws) (cdr choices)))))))

(defun crash (s choices)
  (st (apply-writes (st-durable s) (land (st-pending s) choices)) nil))

(defun fsync-fail (s choices)          ; lands a torn selection, drops the rest
  (st (apply-writes (st-durable s) (land (st-pending s) choices)) nil))
```

Its contracts:

```lisp
(defthm crash-after-fsync-is-the-view
  (equal (st-durable (crash (fsync-ok s) choices)) (view s)))

(defthm crash-keeps-unnamed-blocks
  (implies (and (natp i) (not (names-index-p i (st-pending s))))
           (equal (nth i (st-durable (crash s choices)))
                  (nth i (st-durable s)))))

(defthm fsync-retry-after-failure-adds-nothing
  (equal (st-durable (fsync-ok (fsync-fail s choices)))
         (st-durable (fsync-fail s choices))))
```

Programs are lists of operations, and a crash may happen after any prefix:

```lisp
(defun crash-at (s ops k choices) (crash (run s (take k ops)) choices))

(defun commit-program (v)
  (list (list :write 1 v) (list :fsync) (list :write 0 1)))

(defthm commit-program-marker-implies-data
  (implies (and (null (st-pending s))
                (not (equal (nth 0 (st-durable s)) 1))
                (member-equal k '(0 1 2 3))
                (committedp (crash-at s (commit-program v) k choices)))
           (equal (nth 1 (st-durable (crash-at s (commit-program v) k choices)))
                  v)))
```

Proving that keystone surfaced a rewriting detail worth knowing: with
`nth` and `update-nth` enabled, block reads become `CAR` and `CADR` of
`UPDATE-NTH` terms that nothing simplifies, and the proof stopped at
`(EQUAL (CADR (UPDATE-NTH 1 V (CAR S))) V)`; with both disabled locally,
the built-in `NTH-UPDATE-NTH` decides every read
[measured: the book without its `(local (in-theory (disable nth
update-nth)))`]. fn's paged catalog keeps the same two functions closed for
the same reason [fn: books/catalog-paged.lisp:76-79 @3bbfc4dca].

The teeth are concrete crashes. Without "the marker is not already set",
cut 0 shows the marker over old data; without "nothing is pending", a
pending garbage write to the marker sets it; and the mutated program with
the middle fsync removed has a crash that lands the marker and drops the
data, `(crash-at *s0* (commit-program-no-fence 42) 2 '(:drop :new))`,
whose image is committed with the old value 7 in the data block
[example: examples/systems/crash-store.lisp].

### Where the model is weaker than hardware

A crash model is a claim about the platform, and every freedom it omits is
a behaviour it assumes cannot happen. fn's spec names the ones it leaves
out [fn: specs/crash-model-v2.md:1967-1990 @3bbfc4dca]:

- **Media corruption**: "durable octets change with no pending write". Not
  stated; fn keeps it for a separate salvage model.
- **A lying fence**: "a fence that returns `:ok` without committing: drive
  caches ignoring FLUSH CACHE, `fsync` on darwin without `F_FULLFSYNC`, USB
  bridges ... Not an assumption with a witness; it is the boundary of
  A-CRASH-IMAGE".
- **Non-POSIX namespaces**: "NFS close-to-open, FAT without directory
  fences, overlay and FUSE filesystems, `data=writeback`, ext2 ... no
  theorem holds there and none claims to".
- **Freshness**: "whole-store rollback to an older valid image" is not a
  crash and cannot be expressed.

The papers add three more. Zheng et al. found, in thirteen of fifteen SSDs
under power faults, "bit corruption, shorn writes, unserializable writes,
metadata corruption, and total device failure", where a flying write is
"Well-formed records end up in the wrong place" and unserializability is
"Final state of storage does not result from a serializable operation
order" [paper: zheng2013-ssd-robustness-under-power-fault.txt, abstract
and Table 1 (lines 44-49, 170-183)]. Against the byte model:

- A **flying write** lands a write at another address; the model's garble
  only ever lands inside the range a pending write names, so this is
  excluded, by the same per-inode isolation that SQLite's powersafe
  overwrite states ("a write of a byte range does not damage bytes outside
  the range even on power loss") [fn: specs/crash-model-v2.md:721 @3bbfc4dca].
  A shorn write that damages bytes outside the written range within the
  same sector is excluded the same way: the example's `land` and fn's
  `fn-bs-tear-write` garble exactly the written slice of each unit
  [fn: books/byte-store.lisp:449-475 @3bbfc4dca].
- An **unserializable** final state is one no subsequence of pending
  operations explains; the model admits only subsequences.
- **Process death is not power loss.** fn's qualification evidence is
  "process death only; no power-loss claim"
  [fn: specs/crash-model-v2.md:1934-1935 @3bbfc4dca], and its storage
  analysis turns on the difference: after process death "the NEXT process
  scans the *view*", because pending operations are still in the kernel's
  cache [fn: specs/crash-model-v2.md:1176-1186 @3bbfc4dca]. A model
  validated only by killing processes has not been validated for power
  cuts.

Where it is stronger than its neighbours: FSCQ's disk "states that blocks
are written atomically; that is, after a crash, a block must contain either
the last-written value or one of the previous values, and partial block
writes are not allowed" [paper: chen2015-fscq-crash-hoare-logic.txt, lines
543-552], and Yggdrasil's asynchronous disk "has an unbounded volatile
cache and allows arbitrary reordering" but assumes "a single block
read/write is atomic" [paper: sigurbjarnarson2016-yggdrasil-push-button-crash-refinement.txt,
lines 384-395]. fn's `:garble` and `:zero` units drop that atomicity
assumption.

On ordering and directories the model is deliberately conservative: it
does not encode "`fsync(fd)` incidentally committing the parent directory
entry, which ext4 in practice does for new files"
[fn: specs/crash-model-v2.md:729-731 @3bbfc4dca], although Pillai et al.
found that "Most file systems, however, persist directory entries that the
file is dependent on ... We found that this behavior is required by three
applications for maintaining basic consistency"
[paper: pillai2014-all-file-systems-not-created-equal.txt, lines 1652-1656].
A conservative freedom can only make a program's theorem harder to prove,
never false; an omitted freedom can make it false on the hardware.

What a tougher model looks like, from the papers on the shelf:

- **Crash during recovery.** FSCQ's logic has "recovery execution
  semantics": if the system crashes, "it starts running the recovery
  procedure (perhaps multiple times if there are crashes during recovery)",
  and its recovery specification is idempotent, "since the crash condition
  implies the precondition" [paper: chen2015-fscq-crash-hoare-logic.txt,
  lines 660-686]. fn handles the recovery window as a named predicate
  (`fn-sf-recovery-crash-imagep`, "what a crash may leave, including the
  record the recovery window replayed and has not re-fenced")
  [fn: specs/crash-model-v2.md:1997 @3bbfc4dca].
- **Metadata and data ordering as a specification.** DFSCQ gives "a
  precise specification for fsync and fdatasync" by a "metadata-prefix
  specification ... which roughly follows the behavior of Linux ext4", using
  "tree sequences" to describe "how data writes can be reordered with
  respect to metadata updates" [paper: chen2017-dfscq-verifying-high-performance-crash-safe-fs.txt,
  abstract (lines 7-23)].
- **Concurrency with crashes.** Perennial extends Iris "with three
  techniques to enable crash-safety reasoning: recovery leases, recovery
  helping, and versioned memory" [paper: chajed2019-perennial-crash-safety-concurrency.txt,
  abstract (lines 22-33)]. fn's model has one process.
- **Refinement against a spec of disk states.** Yggdrasil's crash
  refinement "requires the set of possible disk states produced by an
  implementation (including states produced by crashes) to be a subset of
  those allowed by the specification", which is "amenable to fully
  automated satisfiability modulo theories (SMT) reasoning"
  [paper: sigurbjarnarson2016-yggdrasil-push-button-crash-refinement.txt,
  abstract (lines 26-36)].
- **Testing the model against the platform.** CrashMonkey's bounded
  black-box testing "works by exhaustively generating workloads within a
  bounded space, simulating" crashes [paper: mohan2018-crashmonkey-bounded-black-box-crash-testing.txt,
  lines 49-53]; Rebello et al. found that ext4, XFS and Btrfs "mark pages
  clean after fsync fails, rendering techniques such as application-level
  retry ineffective. However, the content in said clean pages varies
  depending on the file system; ext4 and XFS contain the latest copy in
  memory while Btrfs reverts to the previous consistent state"
  [paper: rebello2020-can-applications-recover-fsync-failures.txt, lines
  66-70]. That variation is exactly the "unspecified on purpose" read after
  a failed fence in fn's model.

## 4.3 Discharging an assumption by functional instance

### What goes wrong

A named assumption that no theorem uses is decoration. fn's assumptions
book says so in its own header: "It does not make any theorem depend on
the assumption. Each constraint below carries a comment naming the theorems
that should eventually take it as a hypothesis. Until they do, this book
states the assumptions; it does not yet discharge or apply them"
[fn: books/assumptions.lisp:23-26 @3bbfc4dca], and the proof strategy
repeats it: "The encapsulates state the assumptions; they do not yet apply
them. No theorem in the tree takes one as a hypothesis today"
[fn: docs/proofs.md:834-836 @3bbfc4dca]. The crash-model review calls the
two original ones "strawmen", constraining "set-membership functions over
abstract 'records' and 'units' that no theorem instantiates"
[fn: specs/crash-model-v2.md:64-68 @3bbfc4dca].

The opposite failure is an assumption no function can satisfy, which
proves anything. An `encapsulate` refuses that: "Its satisfiability is
proved once, by the local witness. An assumption no function can satisfy
is a proof that the deployment is impossible, and ACL2 refuses the
encapsulate rather than letting it stand" [fn: books/assumptions.lisp:14-16 @3bbfc4dca].

### The mechanism

"Non-trivial encapsulations provide a way to introduce axioms about new
function symbols, without introducing inconsistency and without
introducing complete definitions" [:doc encapsulate]; the local
definitions "are just 'witness functions' that establish the consistency
of the constraints", and theorems proved about the constrained functions
"may be later functionally instantiated, as with the `:functional-instance`
lemma instance ..., to derive analogous theorems about different functions,
provided the constraints ... can be proved about the new functions"
[:doc encapsulate]. fn's platform step: "Write a concrete function, say
`qual-apfs-image`, that models what the qualified device, filesystem and
barrier call actually preserve across a power cut ... Prove the two
constraints about it ... Then every theorem that took A-DURABILITY as a
hypothesis transfers to that platform by `(:functional-instance <theorem>
(fn-assume-durability-image qual-apfs-image))`, and the transfer is checked
by ACL2 rather than asserted in prose" [fn: docs/proofs.md:821-830 @3bbfc4dca].
The A-DURABILITY encapsulate is two constraints, "a crash cannot lose a
barriered record, and a crash cannot invent one", over a local witness that
keeps exactly the barriered records [fn: books/assumptions.lisp:56-97 @3bbfc4dca].

The example does the whole loop for the crash store: assumption, a theorem
that uses it, the model qualified, and a non-platform refused
[example: examples/systems/assumption-instance.lisp]:

```lisp
(encapsulate
  (((platform-crash * *) => *))
  (local (defun platform-crash (s oracle)
           (declare (ignore oracle))
           (crash s nil)))                    ; the lose-everything image
  (defthm platform-crash-keeps-fenced-view
    (equal (st-durable (platform-crash (fsync-ok s) oracle)) (view s)))
  (defthm platform-crash-keeps-unnamed-blocks
    (implies (and (natp i) (not (names-index-p i (st-pending s))))
             (equal (nth i (st-durable (platform-crash s oracle)))
                    (nth i (st-durable s))))))

(defun acked-commit-program (v)
  (list (list :write 1 v) (list :fsync) (list :write 0 1) (list :fsync)))

(defthm acked-commit-survives-platform-crash
  (let ((img (platform-crash (run s (acked-commit-program v)) oracle)))
    (and (equal (nth 0 (st-durable img)) 1)
         (equal (nth 1 (st-durable img)) v))))

(defthm acked-commit-survives-model-crash
  (let ((img (crash (run s (acked-commit-program v)) choices)))
    (and (equal (nth 0 (st-durable img)) 1)
         (equal (nth 1 (st-durable img)) v)))
  :hints (("Goal" :use ((:functional-instance
                         acked-commit-survives-platform-crash
                         (platform-crash (lambda (s oracle) (crash s oracle))))))))
```

The model's qualification obligations are the two constraints with
`platform-crash` replaced, which `crash-store.lisp` already proved. A
"platform" that zeroes block 1 on every crash fails them; ACL2 reports
"provided we can establish the two constraints generated" and leaves the
subgoal `(EQUAL (NTH I (UPDATE-NTH 1 0 (ST-DURABLE (CRASH S NIL)))) (NTH I
(ST-DURABLE S)))`, false at `i = 1`, and the book records the refusal with
`must-fail` [measured: the `must-fail` body of that book, ungagged].

Two details of the proof are the opaque-record discipline again. The
assumption is stated about `(ST-DURABLE (PLATFORM-CRASH (FSYNC-OK S)
...))`; with `fsync-ok` open, the run's final fence became a `CONS` and the
constraint never matched (the checkpoint showed `(PLATFORM-CRASH (CONS
(UPDATE-NTH 0 1 ...) '(NIL)) ORACLE)`), and with `st-durable` open the read
became `CAR` [measured: the book's drafts]. The book proves
`st-durable-of-fsync-ok` and the record lemmas and closes all four
functions locally. A constraint is a rewrite rule like any other: its
left-hand side has to survive to the goal.

## 4.4 State machines and step functions

### What goes wrong

**A safety theorem is not progress.** fn: "Trace induction lifts one-step
safety properties to finite executions. Eventual delivery additionally
needs a scheduling/contact/resource model and A-FAIRNESS. Do not describe
a safety theorem as proving inevitable delivery"
[fn: docs/proofs.md:71-73 @3bbfc4dca]. The example makes the point with
an admitted trace in which every storage answer is `:timeout`: the queue
keeps its message forever and nothing is ever flushed, and every invariant
still holds [example: examples/systems/step-invariant.lisp].

**An invariant with no inhabitant proves everything.** "An invariant must
include meaningful initial states and reachable examples, so a theorem is
not satisfied by an empty state domain" [fn: docs/proofs.md:68-70 @3bbfc4dca].

**A fourth outcome that reads as success.** fn found a POST handler that
answered a malformed session "with NO EFFECTS, which is not accepted,
refused or uncertain: it is a fourth thing that reads as success, and it is
why the POST miss was invisible for a day"; the fix answers 403 and a
theorem "states that the fourth outcome differs from all three others"
[fn: docs/proof-style.md:830-835 @3bbfc4dca]. In fn's verdict vocabulary,
"`accepted`/`refused`/`uncertain` are D13's outcomes"
[fn: docs/proofs.md:755-757 @3bbfc4dca].

**Opening a recognizer to prove a transition.** fn measured it: "a
`(local (in-theory (enable fn-tcl-sessionp)))` above C2 put its eleven
sub-recognizers into the clause and produced 1082 subgoals; closed, the
same theorem took 0.30 s" [fn: docs/proof-style.md:791-794 @3bbfc4dca].

### The shape of the claims

"State preservation has the schematic form `inv(s) and permitted-event(s,e)
=> inv(next(s,e))`. Prefer total, guarded interfaces that explicitly reject
malformed events rather than assume away untrusted wire inputs"
[fn: docs/proofs.md:65-67 @3bbfc4dca]. The example is a bounded outbox
whose step is total over every event and answers one of three outcomes
[example: examples/systems/step-invariant.lisp]:

```lisp
(defun ob-step (s e)
  ; returns (list outcome new-state)
  (cond ((and (consp e) (eq (car e) :put) (stringp (cadr e)))
         (if (< (len (ob-q s)) (ob-cap s))
             (list :accepted (ob (append (ob-q s) (list (cadr e)))
                                 (ob-flushed s) (ob-doubtful s) (ob-cap s)))
           (list :refused s)))
        ((and (consp e) (eq (car e) :sync))
         (case (cadr e)
           (:ok (list :accepted
                      (ob nil (+ (ob-flushed s) (len (ob-q s))) nil (ob-cap s))))
           (:timeout (list :uncertain
                           (ob (ob-q s) (ob-flushed s) t (ob-cap s))))
           (otherwise (list :refused s))))
        (t (list :refused s))))

(defthm ob-step-outcome-is-typed
  (member-equal (outcome (ob-step s e)) '(:accepted :refused :uncertain)))

(defthm ob-step-refusal-is-no-op
  (implies (equal (outcome (ob-step s e)) :refused)
           (equal (next (ob-step s e)) s)))

(defthm ob-step-preserves-invp
  (implies (ob-invp s)
           (ob-invp (next (ob-step s e)))))

(defthm ob-step-uncertain-keeps-queue
  (implies (equal (outcome (ob-step s e)) :uncertain)
           (equal (ob-q (next (ob-step s e))) (ob-q s))))
```

The `permitted` premise is empty because the step refuses what it does not
permit. The uncertain outcome is the one a storage timeout forces: the
queue may or may not be durable, so it is kept and the state marked.

Trace induction is then one theorem:

```lisp
(defun ob-run (s es)
  (if (atom es) s (ob-run (next (ob-step s (car es))) (cdr es))))

(defthm ob-run-preserves-invp
  (implies (ob-invp s) (ob-invp (ob-run s es))))
```

fn generates it from the one-step theorem by functional instance of a
generic trace theory, proved once over a constrained invariant, guard and
step:

```lisp
(encapsulate
  (((fn-cd-inv *) => *)
   ((fn-cd-okp * *) => *)
   ((fn-cd-step * *) => *))
  ...
  (defthm fn-cd-step-carries
    (implies (and (fn-cd-inv s) (fn-cd-okp s e))
             (fn-cd-inv (fn-cd-step s e)))))

(defthm fn-cd-run-carries
  (implies (and (fn-cd-inv s) (fn-cd-run-okp s es))
           (fn-cd-inv (fn-cd-run s es)))
  ...)
```

[fn: books/def-carried.lisp:175-207 @3bbfc4dca]

### `def-carried`: invariants carried, not recomputed

fn's rule for a served system is that "A whole-state recognizer guards the
executable path; it is never recomputed per operation"
[fn: docs/proof-style.md:269-271 @3bbfc4dca], measured: "`fn-statep` is
Theta(n^2) in Message-ID comparisons and Theta(n*P) in octet checks, and it ran on
every served operation and four times per replayed record"
[fn: docs/proof-style.md:301-303 @3bbfc4dca]. `def-carried` turns the
carrying argument into generated statements: "per transition
`NAME-FN-carries` (the invariant and FN's guard to the invariant of the
state FN returns ...), per open `NAME-FN-establishes` ... and the generated
`NAME-FN-reaches` -- the guard and `:ok` at the witness, proved -- shows the
success reachable ... per bridge `NAME-PRED-bridge`"; "It is refused unless
each generated statement is proved, every declared host entry
(`fn-interfaces`) returning the carried stobj is listed, and the vacuity
probes fail" [fn: docs/proof-style.md:306-319 @3bbfc4dca]. Its header puts
the design principle in four words: "THE STATEMENTS ARE GENERATED. Nothing
reads a declared theorem's statement: THM is only `:use`d, in the minimal
theory, to prove an event this book writes"
[fn: books/def-carried.lisp:23-25 @3bbfc4dca]. The `-reaches` witness
exists because "otherwise a never-true guard or invariant makes every
statement vacuous and the transitions' skipped guards unjustified"
[fn: books/def-carried.lisp:39-46 @3bbfc4dca].

### Never open a recognizer

"A theorem about a transition of a record ... is proved with the
recognizer and every sub-recognizer CLOSED: a named `fn-<x>-closed` theory,
one lemma per branch dismissing the transitions that cannot affect the
property, the content proved at the owning transition, and the theorem
lifted by `:use`" [fn: docs/proof-style.md:760-766 @3bbfc4dca]. fn's
`fn-deftransition` "never edits a statement, it fixes the theory the proof
runs in and pins it AT THE FORM, so a later `in-theory` cannot widen it by
accident" [fn: docs/proof-style.md:781-783 @3bbfc4dca]. The hand-written
shape [example: examples/systems/closed-recognizer.lisp]:

```lisp
; content at each owning transition, recognizer open here only
(defthm sess-recv-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-recv line s))))
(defthm sess-close-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-close s))))
(defthm sess-drain-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-drain s))))

(deftheory sess-closed
  '(sessionp phasep line-listp sess-recv sess-close sess-drain))
(in-theory (disable sess-closed))

; the dispatcher's keystone, everything closed, theory pinned at the form
(defthm sess-step-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-step e s)))
  :hints (("Goal" :in-theory (union-theories
                              '(sess-step sess-recv-preserves-sessionp
                                sess-close-preserves-sessionp
                                sess-drain-preserves-sessionp)
                              (theory 'minimal-theory)))))
```

A subgoal hint does not inherit a `Goal` hint's theory, which is why the
theory is pinned in one place: "An `:in-theory` hint is a theory
*expression*, and ACL2 evaluates it against the current logical world --
not against the theory its parent goal was proved in"; fn measured a
`Subgoal *1/3` enable putting a disabled step back under every subgoal of
a fold [fn: docs/proof-style.md:673-700 @3bbfc4dca].

### A machine over a constrained machine

fn's runtime contract is a state machine whose instances are themselves
machines, constrained rather than defined, so the contract's theorems hold
for every instance that meets the constraint (section 4.1;
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca]). Its invariants are
ownership facts: "The ownership invariant OutstandingUse(h,g) =>
BytesStable(h,g) and not Recyclable(h,g) is `fn-rtc-invp`'s lease clause
plus the two-state theorem `fn-rtc-outstanding-use-is-stable`"
[fn: books/runtime-contract.lisp:89-91 @3bbfc4dca], and its work bound is
a theorem shape: "one step costs at most q + (fn-rtc-step-c config)"
[fn: books/runtime-contract.lisp:98-101 @3bbfc4dca]. The construction is
the generic layer of section 4.6 applied to a whole executor.

## 4.5 Refinement

### What goes wrong

The usual failure is a refinement theorem about the wrong functions: a
true statement about a model that the host does not run. fn's suspect
detector says this is the one thing no shape check can find: "It cannot
see a theorem that is true, non-trivial, and about the wrong subject. 'The
theorem subject is the function the host calls' is a judgment recorded by
hand" [fn: docs/proofs.md:227-231 @3bbfc4dca].

The second failure is a refinement with hypotheses that the deployed
system cannot discharge. fn's recovery keystone has none: "No hypothesis"
[fn: books/owner-checkpoint-open.lisp:100-103 @3bbfc4dca].

### The pattern that worked

fn's owner opens on two paths, from a checkpoint or by full replay, through
one composition: "it extends a checkpoint C over the records after it
(`fn-sco-extend`), then installs the owner from the extended value E";
"From a verified checkpoint C is the decoded file and the records are the
suffix; on a full replay C is the capture of the empty prefix and the
records are the whole history" [fn: books/owner-checkpoint-open.lisp:4-12 @3bbfc4dca].
The keystone and its proof:

```lisp
(defthm fn-owner-recover-from-checkpoint-equals-full-recover
  (equal (fn-ock-recover-extended
          (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
          configs frontier max-conns)
         (fn-ock-recover-full configs frontier (append prefix suffix) max-conns))
  :hints (("Goal"
           :cases ((equal (fn-sn-open-kind
                           (fn-cpo-open-observed configs frontier
                                                 (append prefix suffix)))
                          :ok))
           :use ((:instance fn-ock-open-ok-has-history
                            (events (append prefix suffix)))
                 fn-sco-extend-of-capture-when-history)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-recover-extended fn-ock-recover-full
                                        fn-ock-install
                                        fn-ock-finalize-of-extended-capture)))))
```

[fn: books/owner-checkpoint-open.lisp:104-121 @3bbfc4dca]

The hints are the pattern. The proof runs in `minimal-theory` plus the four
definitions and one lemma it is about, so nothing else in a very large
world can interfere; it splits on the one condition that matters (did the
open succeed); and the two facts it needs come in by `:use`, each a theorem
about a lower layer: the Store open from the extended capture is the full
open (`fn-ock-finalize-of-extended-capture`, itself proved by `:use` of the
Store-level keystone in `minimal-theory`), and an `:ok` open admitted its
history [fn: books/owner-checkpoint-open.lisp:73-98 @3bbfc4dca]. A layer's
refinement is a theorem about functions; the next layer up uses it as a
fact, not as rules to re-run. The corollary fn needs is then a two-line
`:use` of the keystone and the full-open theorem
(`fn-ock-recover-installs-ocl-relation`) [fn: books/owner-checkpoint-open.lisp:134-149 @3bbfc4dca].

The example has the same shape at the size of a ledger
[example: examples/systems/refinement.lisp]:

```lisp
(defun replay-from (s events)
  (declare (xargs :guard (and (balancesp s) (true-listp events))))
  (if (atom events) s (replay-from (apply-event s (car events)) (cdr events))))

(defun capture (prefix) (declare (xargs :guard (true-listp prefix))) (replay prefix))
(defun recover (ckpt suffix)
  (declare (xargs :guard (and (balancesp ckpt) (true-listp suffix))))
  (replay-from ckpt suffix))

(defthm replay-from-of-append
  (equal (replay-from s (append xs ys))
         (replay-from (replay-from s xs) ys)))

(defthm recover-from-checkpoint-equals-full-replay
  (equal (recover (capture prefix) suffix)
         (replay (append prefix suffix))))
```

and then one rung down, the checkpoint stored encoded: `decode` inverts
`encode` on every `balancesp` value, every replayed state is one, and a
checkpoint that does not decode is refused rather than misread:

```lisp
(defthm recover-encoded-equals-full-replay
  (equal (recover-encoded (encode (capture prefix)) suffix)
         (replay (append prefix suffix))))

(defthm recover-encoded-refuses-garbage
  (implies (not (balancesp (decode bytes)))
           (equal (recover-encoded bytes suffix) :refused)))
```

All of these functions are guard-verified, so they are the program and not
a model of it. The teeth include a mutated recovery that ignores the
checkpoint, which the keystone refutes on a concrete prefix and suffix.

### The refinement ladder

fn planned its assurance as rungs: "Abstract executable state: finite
maps/records and event transitions ... Bounded bytes: refine external
parsing/encoding to the accepted object and NNTP domains ... Crash storage
model: relate logical acceptance to records, writes, barriers, recovery,
and checkpoint selection under named platform assumptions ... Concrete
execution: use guard verification and explicit correspondence between
logical maps and efficient representations, including abstract stobjs
where useful ... Multiple nodes" [fn: docs/proofs.md:45-57 @3bbfc4dca].
Each rung is a refinement theorem whose statement is about the functions of
the rung below.

An abstract stobj is the last rung as an ACL2 event: the correspondence
obligations of chapter 3 section 3.9 say that every export's executable
agrees with its logic under the correspondence, in lockstep from the
creator [:doc defabsstobj]. fn's paged catalog chains two: it proves its
obligations "through the old implementation: the VIEW of a paged state is
the old foundation with its rows array replaced by the decoded columns ...
each paged executable SIMULATES the old one on the view exactly"
[fn: books/catalog-paged.lisp:43-50 @3bbfc4dca] -- a refinement of a
refinement, with the cost chapter 3 described.

Crash refinement adds one more obligation, stated by fn as: "Crash
refinement relates a logical transaction history to stable and volatile
storage state. A completed barrier constrains crashes; it does not simply
assert the result we intended to prove. Unacknowledged commits may survive.
Index reconstruction, checkpoint replacement, and compaction require their
own correspondence results" [fn: docs/proofs.md:75-79 @3bbfc4dca].

## 4.6 Functional instantiation and generic layers

### What goes wrong

**The constraints are what every instance must prove, so they must be the
weakest the generic theorem needs.** The example's first monoid
constraints asked for an identity neutral on every argument; the instances
fix their arguments, so `(mop (mid) x)` is not `x` for a non-number, and
the generic theorem's base case stopped at `(EQUAL (MFOLD YS) (MOP (MFOLD
YS) (MID)))` [measured: `examples/systems/generic-fold.lisp` with its first
constraints]. The constraints that worked require the identity to be
neutral only on results of the operation.

**An executable counterpart of a function over constrained functions
cannot run.** "It is often a good idea to disable executable-counterparts
of functions that call constrained functions" [:doc functional-instantiation-example];
the example disables `(:executable-counterpart mfold)`.

**A bad substitution fails with an ordinary checkpoint.** With subtraction
for the operation, ACL2 reports "The hypothesis can be derived from
MFOLD-OF-APPEND via functional instantiation, provided we can establish
the five constraints generated", and the identity constraint reduces to
`(IMPLIES (ACL2-NUMBERP X) (EQUAL (- X) X))` [measured: the
`must-fail` body of `examples/systems/generic-fold.lisp`, ungagged].

### The mechanism

`encapsulate` introduces constrained functions with local witnesses
[:doc encapsulate]; a `:functional-instance` lemma instance substitutes
functions for them, and "the set of proof obligations generated ... is
the set obtained by applying `alist` to all terms, `tm`, such that (a)
`tm` mentions some function symbol in the domain of `alist`, and (b)
either (i) `tm` is the 'constraint' ... on a function symbol ancestral in
`thm` or in some `defaxiom` or (ii) `tm` is the body of a `defaxiom`"
[:doc constraint]. A function defined over constrained functions, like a
fold, is ancestral, so its definition becomes an obligation for the
function that replaces it. "Functional instantiation allows you to prove
theorems 'by analogy' with previous theorems" [:doc functional-instantiation],
and the manual's worked example folds an associative-commutative operation
and instantiates it with multiplication [:doc functional-instantiation-example].
`def-functional-instance` "attempts to define a new theorem based on
functionally instantiating an existing one with a user-provided function
substitution. It looks up the body of the theorem ... in the ACL2 world and
applies the functional substitution" [books: tools/def-functional-instance.lisp:34-56].

The example [example: examples/systems/generic-fold.lisp]:

```lisp
(encapsulate
  (((mop * *) => *)
   ((mid) => *))
  (local (defun mop (x y) (+ (fix x) (fix y))))
  (local (defun mid () 0))
  (defthm mop-assoc
    (equal (mop (mop x y) z) (mop x (mop y z))))
  (defthm mop-left-id
    (equal (mop (mid) x) (mop x (mid))))
  (defthm mop-right-id-on-results
    (equal (mop (mop x y) (mid)) (mop x y)))
  (defthm mop-id-idem
    (equal (mop (mid) (mid)) (mid))))

(defun mfold (xs)
  (if (atom xs) (mid) (mop (car xs) (mfold (cdr xs)))))

(defthm mfold-of-append
  (equal (mfold (append xs ys))
         (mop (mfold xs) (mfold ys)))
  :hints (("Goal" :induct (mfold xs))))

(defthm sum-list-of-append
  (equal (sum-list (append xs ys))
         (plus-fix (sum-list xs) (sum-list ys)))
  :hints (("Goal" :use ((:functional-instance mfold-of-append
                                              (mop plus-fix)
                                              (mid (lambda () 0))
                                              (mfold sum-list))))))

(def-functional-instance concat-all-of-append
  mfold-of-append
  ((mop app) (mid (lambda () nil)) (mfold concat-all)))
```

### Generic layers: one proof per shape

The loop twin of chapter 3 needs one bridge lemma per function. fn's
`def-loop` needs one per shape: "Here each SHAPE's bridge is proved ONCE,
over constrained functions that have no axioms (`fn-dl-f`, `fn-dl-while`,
...), and every instance obtains its bridge by `:functional-instance` of
that one theorem. The obligation ACL2 generates for the instance is the
definitional equation of `NAME` and of `NAME-loop` under the substitution,
which one unfold of each discharges in `minimal-theory`: no instance
induction, no instance hint" [fn: books/def-loop.lisp:14-20 @3bbfc4dca].
The example does it for a filter-map; the constrained functions have no
constraints at all, and the instance's proof uses only its own two
definitions [example: examples/systems/generic-loop.lisp]:

```lisp
(encapsulate
  (((gl-keep *) => *) ((gl-f *) => *))
  (local (defun gl-keep (x) (declare (ignore x)) t))
  (local (defun gl-f (x) x)))

(defun gl-map (xs) ...)          ; the recursion over gl-keep, gl-f
(defun gl-map-loop (xs acc) ...) ; the accumulator loop

(defthm gl-map-loop-is-revappend ; the one induction
  (equal (gl-map-loop xs acc) (revappend acc (gl-map xs))))

(defthm sq-odds-loop-is-revappend
  (equal (sq-odds-loop xs acc) (revappend acc (sq-odds xs)))
  :hints (("Goal"
           :use ((:functional-instance gl-map-loop-is-revappend
                                       (gl-keep (lambda (x) (oddp x)))
                                       (gl-f (lambda (x) (* x x)))
                                       (gl-map sq-odds)
                                       (gl-map-loop sq-odds-loop)))
           :in-theory (union-theories '(sq-odds sq-odds-loop)
                                      (theory 'minimal-theory)))))
```

The summary of that event lists only `(:DEFINITION SQ-ODDS)` and
`(:DEFINITION SQ-ODDS-LOOP)` among its rules: no induction rune
[measured: `(ld "examples/systems/generic-loop.lisp")`]. fn's emitted
events follow the same plan per shape, with the bridge local and a world
table row naming what was generated "so a tool reads the world rather than
a mirror of this macro" [fn: books/def-loop.lisp:60-66 @3bbfc4dca]; its
`:step` instance hint is at [fn: books/def-loop.lisp:830-850 @3bbfc4dca].

The same layering runs through fn's other generators: `def-carried` emits
"the trace theorem `NAME-run-carries` by functional instantiation of a
generic theory" [fn: docs/proof-style.md:316-317 @3bbfc4dca]; the runtime
contract is written once over a constrained instance machine
[fn: books/runtime-contract.lisp:12-15 @3bbfc4dca]; and A-DURABILITY is
discharged per platform by functional instance (section 4.3). In each, the
generic theorem is proved once and the instance owes only its definitions
or its constraints.

## 4.7 Teeth and keystones

### What goes wrong

**A green theorem can say nothing.** fn's detector lists the shapes it has
seen: "closed-theory-corollary -- the entire proof is `:in-theory '(A B)`
over an explicit list of existing theorems ... instance-corollary -- the
conclusion is an existing theorem's conclusion instantiated, and every
hypothesis of that theorem is already a hypothesis here ...
reflexive-conclusion -- a conjunct of the conclusion is `X R X` ...
definition-restated -- the conclusion is the body of a function it calls
... recognizer-body-conclusion -- the conclusion is the body of a
hypothesis's own recognizer ... branch-of-definition -- a hypothesis is a
branch test of the function under discussion, or its negation, and the
conclusion is exactly that branch's value" [fn: docs/proofs.md:199-218 @3bbfc4dca].
And its limits: it "unfolds only non-recursive definitions and only to a
bounded depth, so a tautology reachable through a recursive function is
invisible to it"; it "cannot see a theorem that is true, non-trivial, and
about the wrong subject"; "The absence of a flag is not evidence of
strength. Teeth are" [fn: docs/proofs.md:220-235 @3bbfc4dca].

**A negated `must-fail` is not a counterexample.** "Never a general negated
`must-fail`: it proves that the prover could not find a proof, which is not
a counterexample, and it loops when the negation is unprovable rather than
false" [fn: docs/proof-style.md:381-383 @3bbfc4dca].

**A violating value outside the guard stops the assertion, not the
theorem.** In `examples/modelling/opaque-record.lisp` the first draft of a
removal witness called the transition with a non-string group and got
"The guard for the function call (ART-CROSSPOST G M), which is (AND
(STRINGP G) (ARTP M)), is violated by the arguments"; fn's contract is that
such a value "is evaluated under `with-guard-checking :none` only by that
declaration" [measured: that draft] [fn: docs/proof-style.md:364-367 @3bbfc4dca].

### The rule

"A keystone ships with a reachable non-degenerate witness and one concrete
violating value per hypothesis, each an `assert-event` on the negated
conclusion" [fn: docs/proof-style.md:349-351 @3bbfc4dca]. "Never a
trivially true assertion. If no violating value exists for a hypothesis,
the hypothesis is unnecessary: delete it from the theorem and say so ...
or record it open with the reason" [fn: docs/proof-style.md:383-388 @3bbfc4dca].
Where a violating value exists but cannot be evaluated, "a `must-fail` of
the weakened statement is only the prover's refusal: label it in the
comment block directly above it, `; teeth: prover-refusal REASON`"
[fn: docs/proof-style.md:388-394 @3bbfc4dca].

`assert-event` is the instrument: it "provides a flexible way to check that
evaluation of an expression returns a non-`nil` value, causing an error
otherwise. Calls of `assert-event` are event forms; thus, they may occur in
books" [:doc assert-event]; `:stobjs-out` lets it check multiple values,
and by default it is skipped when proofs are skipped (`:on-skip-proofs`)
[:doc assert-event].

Each systems example carries its teeth this way. For the outbox keystone
`ob-step-preserves-invp` [example: examples/systems/step-invariant.lisp]:

```lisp
; positive witness: reachable, hypothesis true, conclusion true after a change
(assert-event
 (let ((s (ob-run *s0* '((:put "a")))))
   (and (ob-invp s) (ob-invp (next (ob-step s '(:put "b")))))))

; removal witness for the one hypothesis
(assert-event
 (let ((bad (ob '("a" "b" "c") 0 nil 2)))
   (and (not (ob-invp bad))
        (not (ob-invp (next (ob-step bad '(:sync :timeout))))))))

; mutation: the step without its capacity check is caught at this witness
(assert-event
 (let ((s (ob '("a" "b") 0 nil 2)))
   (and (ob-invp s)
        (not (ob-invp (next (ob-step-mutant s '(:put "c"))))))))
```

The crash store's teeth are three removal witnesses and one mutated
program [example: examples/systems/crash-store.lisp]; the refinement's are
a reachable witness and a mutated recovery [example: examples/systems/refinement.lisp];
the closed-recognizer keystone has a witness and a removal
[example: examples/systems/closed-recognizer.lisp].

### `defteeth` and `defkeystone`

fn made the contract a macro. "`(defteeth NAME :claim (((L H) ...) C) ...)`
binds the teeth to the theorem as the world stores it (the claim is
translated and compared), runs the positive witness and every bound
witness UNDER the guards, runs a removal or mutation logically only when
its entry says `:logical "why"` (recorded in the row and counted as debt),
takes mutations as checked edits of the claim with a named fault, states
cost bounds (`:visits`, `:allocation`) with the state that attains them"
[fn: docs/proof-style.md:352-360 @3bbfc4dca]. The form
[fn: books/defkeystone.lisp:13-42 @3bbfc4dca]:

```lisp
(defteeth NAME
  :claim (((L1 H1) ... (Ln Hn)) C)      ; labelled source hypotheses and the conclusion
  [:subject FN]                         ; the host-called function
  :witness ((VAR VAL) ...)              ; the positive witness, executable
  :breaks ((Li ((VAR VAL) ...) [:logical "why outside the guard domain"]
               [:lemma THM]) | (Li (:assumption FN)) ...) ; one per Li
  :mutations ((L (:conclusion C2) | (:hypothesis Li H2) ((VAR VAL) ...)
                 :fault "the fault it models" [:logical "why"] [:lemma THM]) ...)
             | (:not-applicable "why") | (:deferred "why")
  [:visits (...)] [:allocation (...)]
  [:must-fail t])

(defkeystone NAME TERM :subject FN ... . SPEC)  ; = (defthm NAME TERM ...) then defteeth
```

Three of its rules are worth taking whole. Binding: "When the form runs,
`(implies (and H1 .. Hn) C)` is TRANSLATED in the current world and must
be EQUAL to `(getpropc NAME 'theorem)`; else the form is refused"
[fn: books/defkeystone.lisp:48-51 @3bbfc4dca]. Mutations: "CHECKED EDITS of
the claim, never a free term, each naming the FAULT it models ...
`(:conclusion C2)` is the claim with C2 for C (refused when C2 is C, nil or
t) ... a deferred mutation is not a tooth" [fn: books/defkeystone.lisp:124-133 @3bbfc4dca].
And must-fail: "OFF by default: a must-fail is proof-search exhaustion
within a step limit, not a counterexample; the evaluated witnesses are the
teeth" [fn: books/defkeystone.lisp:148-150 @3bbfc4dca].

### Where to put the effort

fn ended its cut with the owner's narrowing of the obligation: "Ember
(2026-10-17): we only need to demonstrate that our top-level theorems are
not vacuous; the rest fall from use via that"; non-vacuity is "owed once,
here, at the top: for each theorem named in this section 5.4 writes a
must-fail book inside ACL2 ... and a satisfiable-premise witness. A lemma
that turns out vacuous is an ugly argument, not a hole in the ledger"
[fn: OWED.md:11-21 @3bbfc4dca].

So: every keystone has a positive witness that is reachable, a violating
value per hypothesis, and at least one mutation that a plausible bug would
make; lemmas below it earn their keep by being used. The detector's shapes
are worth checking by eye before a theorem is called a keystone, and its
silence is worth nothing.

## 4.8 What to take from this chapter

- Effects are data: actions out, completions in, every outcome an
  argument. Then a theorem can quantify over what the platform answers.
- A crash model is a list of freedoms. Write down the ones it omits, next
  to the evidence that the platform lacks them, and know whether that
  evidence covers power loss or only process death.
- An assumption is an `encapsulate` with a witness, a theorem that uses it,
  and a functional instance that discharges it. Without the second and
  third it is prose.
- Prove one-step safety with the recognizer closed, lift it by trace
  induction, and do not call it progress.
- A refinement keystone with no hypothesis, proved in `minimal-theory`
  from the layer below's keystones, is the shape that survived.
- Prove a shape once over constrained functions; instances owe only their
  definitions.
- A keystone without teeth is not evidence. A reachable witness, a
  violating value per hypothesis, a mutation that bites.
