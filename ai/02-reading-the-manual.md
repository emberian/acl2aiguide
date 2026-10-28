# AI 02. Reading the manual, and ACL2 as a tool

Load this whole before you look anything up or run ACL2. It says how to read
the manual from a shell, which REPL commands answer which question, and how to
run ACL2 from an agent so that one run answers many questions. Everything here
was run on the laptop (ACL2 8.7 on SBCL 2.6.8,
`~/tools/acl2-fn/acl2-literal-4g-tls64k`); `[measured: ...]` names the run.

## 1. Pitfalls first

1. **Technique from memory.** Every option, keyword and obligation you write
   must be read first, in the manual or a book. The manual is a file on this
   machine; reading a topic costs one `sed` (section 2).
2. **`:doc` at the REPL does not know community-book topics.** In a plain
   session `:doc must-fail` answers "There is no documentation for
   MUST-FAIL" [measured: `:doc must-fail` piped into the laptop REPL]; the
   topic is a `defxdoc` in `std/testing/must-fail.lisp`, and `:doc` reaches
   book topics only "when the xdoc system has been included" [:doc doc]. Grep
   the books instead (section 2.3).
3. **A topic name that does not exist.** Check it before citing:
   `grep -c '^(defxdoc NAME$' acl2-doc.lisp` must print 1.
4. **One form per ACL2 run.** Each run pays startup, includes and your wait;
   the lesson ember drew from the fleet is the opposite habit (section 6).
5. **Inhibiting `prove` output hides the checkpoint.** With
   `(set-inhibit-output-lst '(prove event summary proof-tree))` a failed
   `defthm` printed its goal names and `ACL2 Error [Failure]` and no
   checkpoint [measured: `(defthm f1-bad (implies (natp x) (< 5 (f1 x))))`
   under that setting, laptop REPL]. Shrink output with `set-gag-mode`, not by
   inhibiting `prove`.
6. **A stale session.** The REPL refuses to redefine a changed function and
   keeps the old one (section 5.3).
7. **An `ld` that stopped at the first error.** `ld` defaults to
   `:ld-error-action :return!` (section 5.2).

## 2. The manual from a shell

### 2.1 Where it is

ACL2 8.7's manual is the file
`~/tools/acl2-fn/acl2-8.7/books/system/doc/acl2-doc.lisp`, one
`(defxdoc TOPIC ...)` form per topic; `wc -l` and `grep -c '^(defxdoc '` give
its size and topic count [measured: those two commands on the file, laptop].
The text is XDOC markup: `@('x')` is code, `@({ ... })` a code block,
`@(see topic)` and `@(tsee topic)` links.

### 2.2 Read one topic

```sh
D=~/tools/acl2-fn/acl2-8.7/books/system/doc/acl2-doc.lisp
T=with-local-stobj
start=$(grep -n -i "^(defxdoc $T\$" $D | head -1 | cut -d: -f1)
end=$(awk -v s=$start 'NR>s && /^\(defxdoc /{print NR-1; exit}' $D)
sed -n "${start},${end}p" $D
```

The `$` after the name matters: without it `defstobj` also matches
`defstobj-element-type`. A topic can be long (`defabsstobj` is several hundred
lines); read it whole before writing the shape it governs, then quote it.

To find a topic when you know only a word:

```sh
grep -n '^(defxdoc [^ ]*stobj' $D            # topic names containing "stobj"
grep -n ':short ".*time limit' $D            # one-line summaries
```

### 2.3 Community-book topics

They are `defxdoc` forms in the books themselves:

```sh
B=~/tools/acl2-fn/acl2-8.7/books
grep -rn '(defxdoc must-fail$' $B/std/testing/
grep -rn '(defxdoc cert.pl$' $B/build/
```

`std/testing/must-fail.lisp:17` is `must-fail`; `build/doc.lisp` holds
`cert.pl` and its steps (`pre-certify-book-commands` at line 558,
`custom-certify-book-commands` at 673) [books: build/doc.lisp:34];
`doc/practices.lisp` holds `best-practices` (line 36) and
`theory-management` (line 409) [measured: `grep -n '(defxdoc'
books/doc/practices.lisp`, laptop]. Cite these as `[books: PATH:LINE]`.

### 2.4 Rendered, at the REPL

```sh
printf ':doc defabsstobj-missing-events\n(quit)\n' \
  | timeout 60 ~/tools/acl2-fn/acl2-literal-4g-tls64k 2>&1 \
  | sed 's/\x1b\[[0-9;]*m//g'
```

The REPL started and answered in 0.13 s of wall time [measured: that command
with two `:doc` forms under `/usr/bin/time -p`, laptop]. The rendering turns
links into `[topic]`. Use it for reading; quote from the source (2.2), whose
words are the same.

### 2.5 The Emacs browser

ACL2-Doc is "A custom Emacs browser for reading ACL2 documentation" that reads
the combined manual (ACL2 plus books) [:doc acl2-doc]. It needs Emacs; an
agent uses 2.2 to 2.4.

## 3. Which REPL command answers which question

| question | command | source |
| --- | --- | --- |
| what does the manual say | `:doc name` | [:doc doc] |
| formals, guard, signature, type of `f` | `:args f` | [:doc args] |
| the event that introduced `name` | `:pe name` | [:doc pe] |
| which rules could rewrite this term | `:pl (f x)` | [:doc pl] |
| what rules did this event store, enabled or not | `:pr name` | [:doc pr] |
| one command | `:pc name` | [:doc pc] |
| commands back through one | `:pbt name` | [:doc pbt] |
| undo back through one | `:ubt name` | [:doc ubt] |
| is `f` guard-verified | `(symbol-class 'f (w state))` | [example: examples/shapes/defun-guards.lisp] |

What they printed [measured: the forms below in the laptop REPL]:

- `:args f1` after `(defun f1 (x) (+ x 1))`: `Formals: (X)`, `Guard: T`,
  `Guards Verified: NIL`, `Defun-Mode: :logic`, `Type: (ACL2-NUMBERP (F1 X))`.
- `:pbt 1` after that `defun` and one `defthm`: `L 1 (DEFUN F1 (X) ...)` and
  `2:x(DEFTHM F1-POS ...)`. `:ubt f1` undid both: "`Pbt` will print the
  commands that `ubt` will undo" [:doc pbt].
- `:pl (mag x)` in `examples/shapes/driver.lsp`: both rewrite rules about
  `mag` with their hypotheses, the disabled definition, the type
  prescription.
- `:pr mag-when-negative`: `Rune`, `Enabled`, `Hyps`, `Equiv`, `Lhs`, `Rhs`,
  `Backchain-limit-lst`, `Loop-stopper`.

`:pr` "does not print congruence rules, equivalence rules, or refinement
rules", and induction rules made by definitions do not show up [:doc pr].
`:pl` shows rules that are possibly applicable; heuristics may still stop them
[:doc pl].

## 4. What to read for what

Before you write the form, read the topic it is governed by, whole:

| writing | read |
| --- | --- |
| a `defun` | `defun`, `xargs`, `guard`, `verify-guards` |
| a hint | `hints`, `goal-spec`, `lemma-instance`, `using-enabled-rules` |
| a rule | `rule-classes`, then the class (`rewrite`, `linear`, `forward-chaining`, ...), `free-variables` |
| a theory event | `theories`, `in-theory`, `e/d`, `theory-invariant` |
| a stobj | `stobj`, `defstobj`, `with-local-stobj`, `nested-stobjs`, `defabsstobj` |
| an `mbe` | `mbe`, `guards-and-evaluation` |
| a book | `books`, `certify-book`, `include-book`, `local`, `portcullis`, `defpkg`, `book-hash` |
| a failed proof | `the-method`, `introduction-to-key-checkpoints`, `set-gag-mode`, `accumulated-persistence`, `break-rewrite` |

Each of those names was checked with `grep -c '^(defxdoc NAME$'` against
`acl2-doc.lisp`. `ai/01-form-shapes.md` has the forms they govern.

## 5. ACL2 as a tool from an agent

### 5.1 One session, a driver file, read the output once

```sh
cd <repo>/examples/shapes
timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < driver.lsp > driver.out 2>&1
grep -n 'ACL2 Error\|FAILED\|Q.E.D\|key checkpoint' driver.out   # then read the hits whole
```

The driver (`examples/shapes/driver.lsp`, shown whole in
`ai/01-form-shapes.md` section 16) sets the output, includes the certified
closure of the book under work (seconds, no proofs), then runs every attempt.
Rules:

- **Every run under `timeout`.** A form under the shell's `timeout` is cut by
  the signal and reported as an ordinary failure: a guard proof cut at 120 s
  printed `Time: 119.49 seconds (prove: 0.00, print: 0.00, other: 119.49)`,
  "No checkpoints to print" and `FAILED` [measured: the `bench-stobj` draft
  of humans/05 section 5.2, laptop REPL]. A `FAILED` at your own limit is
  your limit, not ACL2's verdict.
- **Every event under `with-prover-time-limit`** in a driver, so one search
  that does not return costs seconds and not the session; the limit is CPU
  time and "if ACL2 notices this fact during a proof, then that proof will
  abort" [:doc with-prover-time-limit]. fn's live-session tool wraps every
  event it sends that way [fn: docs/proofs.md:489 @3bbfc4dca].
- **Read the output once**, from the first error, whole. Do not rerun to
  search output; save it to a file and grep it.
- **Anything longer than a tool call's limit runs in the background**, with a
  PID file, and you continue working; fn's lane record: "`send-file` of a
  long run exceeds a 120 s tool timeout: run it in the background"
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:25 @worktree].
  Never a foreground `sleep` loop (`ai/00-pitfalls-first.md`).

### 5.2 Batching with `ld`

```lisp
(ld '((defthm a ...) (defthm b ...) (defthm c ...))
    :ld-pre-eval-print t
    :ld-error-action :continue)
```

or `(ld "attempts.lsp" :ld-pre-eval-print t :ld-error-action :continue)` for
a file of forms [:doc ld].

- `:ld-error-action :continue`: without it, "the default value for
  `ld-error-action` on calls of `ld` is `:return!`", which stops at the first
  error; with `:continue`, `ld` "just continues processing the forms"
  [:doc ld-error-action]. Forms piped into the top-level loop continue past
  errors by default (its initial value is `:continue`)
  [:doc ld-error-action].
- `:ld-pre-eval-print t` prints each form before it runs, "useful if you are
  reading from a file of commands and wish to assemble a complete script of
  the session" [:doc ld-pre-eval-print]; the output then says which result
  belongs to which form.
- In one measured run, a batch of three `defthm`s gave a proof, an illegal
  rule and a failed proof with its key checkpoint, all in one output
  [measured: examples/shapes/driver.lsp, laptop].

### 5.3 Output to read, and output to drop

- `(set-gag-mode :goals)`, the default: "only key checkpoints are printed",
  plus each goal's name as it is generated [:doc set-gag-mode]. `(set-gag-mode
  nil)` prints the whole narration; `:pso` prints what gag mode saved
  [:doc pso].
- `(set-inhibit-output-lst '(proof-tree))` drops a kind of output; the kinds
  include `error`, `warning`, `observation`, `prove`, `event`, `history`,
  `summary`, `proof-tree`, `comment` [:doc set-inhibit-output-lst]. Do not
  inhibit `prove` while debugging (pitfall 5). Keep `summary`: its `Time:` and
  `Prover steps counted:` lines are the measurements
  [fn: docs/proof-style.md:591 @3bbfc4dca].

### 5.4 A session is a world; an edit needs a new one

```
ACL2 Error in ( DEFUN F1 ...):  The name F1 is in use as a function.
Note that the proposed body for F1,

(+ X 2),

differs from the existing body,

(+ X 1).

The redefinition feature is currently off.  See :DOC ld-redefinition-
action.
```

After that error `(f1 3)` still returned `4` [measured: `(defun f1 (x) (+ x
1))`, `(defun f1 (x) (+ x 2))`, `(f1 3)`, laptop REPL]. "When
`ld-redefinition-action` is `nil`, redefinition is prohibited"; turning it on
means "ACL2 is liable to be made unsafe or unsound" [:doc
ld-redefinition-action]. After editing a book: start a new session, or `:ubt`
back past the first changed event and resubmit from there [:doc ubt]. fn's
lane rule: "The REPL refuses to redefine a changed function: after editing a
book or test, stop and restart the session"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:24 @worktree].
Transcripts show the same refusal for theorems, cured by `ubt!` and a replay
from the changed event [cv: agent-aa0987d97e41cae69#143].

A session loaded form by form also keeps `local` events that a certified
include would drop: a dependent admitted in such a session failed
certification (fn's octets-bulk case), and fn's REPL tool then wrapped each
source-loaded book in `(encapsulate () ...)` to drop its locals
[cv: agent-a8f0054be0cd5b5a3#287]. A REPL admission is not a certificate:
"A form ACL2 admits there is not a certificate; the event goes into the book
and the book certifies" [fn: docs/proofs.md:506 @3bbfc4dca].

## 6. The batching rule

ember, to an agent fleet on 2026-10-27: "it's something systematic about they
way we're using lake and iterating one statement at a time instead of
iterating across the whole system and using mental simulations and reasoning
in our mind to metarationally develop without wasteful rerun loops of
bullshit slow things" [fn: build/coordinator/EMBER.md:392 @worktree]. (The
words were about Lean's `lake`; the habit is the same in ACL2.) The procedure:

1. **Simulate the proof first.** Write down the induction you expect and the
   lemmas the simplifier will need, as The Method says: "Think about the proof
   first" and "Prove the lemmas the proof needs first" [:doc the-method].
   Evaluate the conjecture on small values, including the non-list, zero and
   short-list cases, before proving anything
   [example: examples/prover/false-conjecture.lisp].
2. **Write the whole book**: definitions, lemmas, the keystone, its teeth
   (`ai/01-form-shapes.md` section 11).
3. **Run it once**: a driver that includes the certified dependencies and
   `ld`s the book's forms with `:ld-error-action :continue`, every event under
   a time limit.
4. **Read every checkpoint** in that output, from the first failure, as The
   Method says: "inspect the failed proof attempt, starting from the beginning,
   not the end" [:doc the-method].
5. **Fix all of them**, then run again. After any repair, "Start over trying
   to prove your main conjecture ... Do not just scroll back to the key
   checkpoints generated the last time" [:doc introduction-to-key-checkpoints].
6. **Certify once** with `cert.pl` when the driver run is clean (section 7).

Never one form per run. The transcripts show the cost of the per-form loop in
tooling terms: a lane recorded that "Each proof_repl start on hbox takes about
20 to 40 s of sync and install, so revalidating 23 books took about 10 minutes
of waiting" [cv: agent-a6a9830e48f770119#502], and another asked for its probe
tool to accept several forms at once ("`probe --form -` refuses more than one
form") [cv: agent-a465001fb558f6b6c#0]. The lane that cleared twelve looping
teeth in one sitting did it with multi-form scratch drivers (`teeth3.lsp`,
`teeth4.lsp`, `teeth5.lsp`), each probing many teeth per run
[cv: agent-a0eaf22c912c1c1fe#97], [cv: agent-a0eaf22c912c1c1fe#203], and
committed all twelve together [cv: agent-a0eaf22c912c1c1fe#230].

## 7. `cert.pl` for closures, and what a certificate covers

### 7.1 Certify the changed book yourself

```sh
cd <repo> && examples/certify.sh shapes/hints.lisp
```

prints `Built .../shapes/hints.cert (0.514s) at ...` on success and
`**CERTIFICATION FAILED** for <book>` on failure [measured:
`examples/certify.sh` on the books of examples/shapes, laptop]. `cert.pl`
"will rebuild exactly the necessary books, in parallel" [books:
build/doc.lisp:34]. The certificate is the verdict: a failed certification's
log ended `Exit code from ACL2 is 0` and a successful one's `Exit code from
ACL2 is 43` [measured: the `.cert.out` of a failed and of a successful
certification in examples/shapes]; fn's driver had the same trap, "a book that
failed still exits 0" [fn: docs/proofs.md:607 @3bbfc4dca].

Certify before you report: "a lane certifies what it changed and its test
books on the farm before it reports" [fn: docs/proofs.md:469 @3bbfc4dca].
Use `cert.pl` for closures (it orders and parallelizes the includes); use the
REPL driver for search (section 6). A closure run "stops at the first red
book, and every book above reads 'There is no certificate on file'"
[fn: docs/proofs.md:554 @3bbfc4dca]; read the first red, not the cascade
(`ai/00-pitfalls-first.md`).

### 7.2 What a certificate records

`certify-book` writes "a certificate recording not only that the book was
certified but also recording the commands necessary to recreate the
certification world ... and a book-hash for each of the books involved"
[:doc certify-book]. Every included book must already be certified: "An
error will occur if `certify-book` has to deal with any uncertified book other
than the one on which it was called" [:doc certify-book]. The portcullis is
"a list of commands used to create the ``certification world'' and an alist
specifying book-hash values for all the books included in that world"
[:doc portcullis].

"By default, a book-hash is an alist that records, for a given book (`.lisp`
file), its file size (in bytes) and its write-date"; to use a checksum, "set
environment variable `ACL2_BOOK_HASH_ALISTP` to `NIL`" before starting ACL2
[:doc book-hash]. `examples/certify.sh` sets it (since `ACL2_BOOK_HASH_ALISTP`
was found unset there, with the certificates carrying `BOOK-WRITE-DATE` and
`BOOK-LENGTH` [measured: `examples/shapes/pkg-book.cert` after
`examples/certify.sh shapes/pkg-book.lisp`, before the fix, laptop]); under
the default, copying or touching a book invalidates its certificate: the
transcripts show includes refused with "The
certificate for ... lists the book-hash of that book as ((:BOOK-LENGTH .
19852) (:BOOK-WRITE-DATE . 3998706531)). But its book-hash is now computed to
be ((:BOOK-LENGTH . 19852) (:BOOK-WRITE-DATE . 3998719948))" -- same length,
new date [cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#549] -- and a whole
certificate cache found "POISONED" the same way [cv:
agent-a90a1032ade59e64c#171].

fn's rule, after those incidents: "Every fn tool that starts ACL2 sets
`ACL2_BOOK_HASH_ALISTP=NIL`, so ACL2 8.7 hashes book *contents* rather than
write dates and absolute paths" [fn: docs/proofs.md:295 @3bbfc4dca], and "a
certificate is valid only for a book *and every book it includes*, so the key
is the SHA-256 of the sorted `<path>:<sha256>` listing of the book and its
whole local include closure" [fn: docs/proofs.md:308 @3bbfc4dca]. On SBCL the
`.fasl` is loaded only when not older than the `.cert`, so a certificate
copied without its `.fasl` "loads uncompiled" [fn: docs/proofs.md:351
@3bbfc4dca].

## 8. Not covered here

- `xdoc::save` (writing the HTML manual) exists as a topic in
  `books/xdoc/topics.lisp`; this guide did not run it on the laptop, so it
  gives no recipe for it.
