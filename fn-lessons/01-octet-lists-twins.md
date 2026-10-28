# 01. Octet lists at runtime: asked for six times, landed as twins

## The wound

Ember asked for the same thing six times in five weeks, and twice more as
recorded decisions: no octet lists at runtime, a concrete representation
(stobj byte arrays, an arena with handles, u64 column pages and a byte pool),
and the list kept only as the logical model
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:42 @worktree]. The
first time, on 2026-09-25: "Using octet lists continues to be unacceptable at
runtime :) ... Octet lists are absurd amount of overhead! Let's endeavor to
have efficient representations ;) Otherwise the software is not useful as a
system" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:17 @worktree]
(its citation: `720920b2#430`). On 2026-10-05, after a report of "Byte work
done in Lisp, one octet at a time ... about 6 us per octet": "at one point we
had did an TRULY ENORMOUS development wave focused entirely on efficient
concrete representation and never using a linked list of octets for any
purpose whatsoever, and.... ugh, it seems like all of that got blasted
away..... and we have accidentally quadratic algorithms back in play again!"
[fn: build/coordinator/EMBER.md:218-220 @worktree] [cv: be1e9dcf#2198]. On
2026-10-28: "do we still have so much scar tissue that we lost our efficient
stobj representation?" [fn: build/coordinator/EMBER.md:423 @worktree].

Nothing had been lost. The octet buffer, the payload arena, the paged
catalog, the linear-hashing Message-ID pages and the paged history all landed
and are attached; "What did not happen is the second half of each landing:
deleting the list path it was built to replace"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:48 @worktree]. The
measure is the host's conversion `fnn-octet-list`, which is `(coerce octets
'list)` [fn: host/native/io.lisp:264-265 @3bbfc4dca]. Its direct calls in
`host/` were 130 on 2026-09-22, 179 on D27's day, 238 at D41, 252 at the
freeze and 263 from 2026-10-14 to `origin/dev`: "The count grew in every
period after D27" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:50-61 @worktree].
Re-measured at the pinned sha: 263
[measured: `git -C ~/dev/fn grep -h -o -E '\(fnn-octet-list ' 3bbfc4dca -- host | wc -l`, 2026-10-28, laptop].
The shrink-only lint built for it, `tools/list_codec_check.py`, has stood at
92 sites since 2026-10-02 [fn: tools/list_codec_baseline.json @3bbfc4dca],
and the POST path still changes the article's representation 18 times between
socket and log (lesson 02).

The cause is a written law. D27 said: "**The logical model stays octet lists;
the executable path does not.** Record bodies, frames, headers, the Message-ID
index and the in-memory history get concrete representations ... with a
correspondence theorem to the list definition at every boundary the host
calls" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:18 @worktree].
That law "made each new buffer path a **twin** of a list path, proved equal to
it. The list path stayed callable, and new host code kept calling it"; D62
named the result "494 loop twins and 285 representation twins"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:136 @worktree]. The
lint's own instructions repeat the law: "Only shrinks: give the codec a buffer
twin with its boundary theorem ... and lower its count"
[fn: tools/list_codec_baseline.json @3bbfc4dca].

## What was done about it

- Each representation wave landed its buffer path with a correspondence
  theorem: `fn-octets` (wave B), the subject digest over the buffer (wave C),
  the payload arena (wave D), checkpoint read and write through the buffer
  (N=10,000 x 32 KiB reopen from 4.80 to 2.22 GB VmRSS), the log entry decided
  in the buffer, the D41 column pages
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:120-134 @worktree].
- A shrink-only lint was built and then not driven: 99 to 92 sites, unchanged
  since 1776d0191 on 2026-10-02
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:61 @worktree].
- The M1 cut deleted unreached books and therefore no running list path: "the
  `fnn-octet-list` count is 263 before and after"
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:159 @worktree].
- The 2026-10-28 investigation names the decision a rebuild settles first:
  "What *is* an article's bytes, as one value with one owner, from the socket
  read to the log write? ... with the octet list confined to `:logic` and
  never callable from `:exec`", and the deletions that go in the same landing:
  `fnn-octet-list`'s calls to zero on the served path; `fn-octets-list`,
  `fn-arena-payload` and `fn-arena-seal-list` out of the exec closure;
  packed-submission and body-chunks "deleted, not twinned"
  [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:183-186 @worktree].
- The successor project's law replaces D27's: "The derived path is the ONLY
  path. Nothing lands beside what it supersedes; everything replaces; delete
  the twin" [file: ~/dev/minidregg/CLAUDE.md, "The laws that bind every
  session here"].

## The lesson

A correspondence theorem is the proof that a new path may replace an old one,
not a licence to keep both; a landing that adds the concrete path deletes the
list path in the same commit, or it has not landed. Make the list view
impossible to call from executable code: define it with `defun-nx` and leave
its guards unverified, so "the calls of the resulting function cannot be
evaluated" [:doc defun-nx], and any guard-verified function that calls it
outside the `:logic` half of an `mbe` is refused when it is admitted; in an
`mbe` "only the `:exec` code is evaluated" in a guard-verified body, and the
equality of the two halves "is proved when verifying guards" [:doc mbe]. A
shrink-only count is a ratchet only if some landing is required to move it to
zero.

## The shape to copy

The list view is `defun-nx` with no guard; the function the host calls states
its logic over the view and executes on the real representation; a walk of
the view in executable code does not get admitted
[example: examples/fn-lessons/list-view-nonexec.lisp]:

```lisp
(defun-nx payload-octets (s)
  (codes-of (coerce s 'list)))

(defun payload-len (s)
  (declare (xargs :guard (stringp s)))
  (mbe :logic (len (payload-octets s))
       :exec (length s)))

(local
 (must-fail
  (defun payload-len-by-walk (s)
    (declare (xargs :guard (stringp s)))
    (len (payload-octets s)))))
```

The refusal reads "The body for PAYLOAD-LEN-BY-WALK calls the function
PAYLOAD-OCTETS, the guards of which have not yet been verified"
[measured: the `must-fail` body of examples/fn-lessons/list-view-nonexec.lisp
sent to the laptop REPL after including the book, ACL2 8.7 / SBCL 2.6.8]. Two
limits, both measured the same way: a view given a guard (and so
guard-verified) lets the caller be admitted and fails only when called ("ACL2
cannot ev the call of non-executable function"), and a caller whose own guards
are not verified is admitted too. So the shape holds when every executable
function is guard-verified, which is what fn's ledger already demands of any
function cited as evidence [fn: docs/proofs.md:194-195 @3bbfc4dca]. The
correspondence proof itself is one `mbe` per function (chapter
`humans/02-rewriting-theories-books.md` section 2.9.6 for what the book then
exports), never a second callable definition.
