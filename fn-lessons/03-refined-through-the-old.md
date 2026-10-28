# 03. A new representation refined through the old one keeps the old one: the nested catalog and the third catalog

## The wound

D41 (2026-10-01) asked for one catalog: "The store's live state becomes typed
u64 column pages plus a byte pool ... so the on-disk and in-memory images are
the same bytes" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:31 @worktree].
The paged catalog that answered it proves its correctness by simulating the
old implementation, and to do that it carries the old implementation inside
itself: "here they are the old foundation `fn-cat$c` NESTED whole, its rows
array repurposed as the overflow cells, and every table operation is the old
executable called through `stobj-let`"; "THE PROOF is a refinement through the
old implementation: the VIEW of a paged state is the old foundation with its
rows array replaced by the decoded columns ... each paged executable
SIMULATES the old one on the view exactly ... and every obligation
`defabsstobj` states is the old obligation instantiated at the view"
[fn: books/catalog-paged.lisp:37-51 @3bbfc4dca]. The foundation's field list
says it outright: `(fn-cat$p-tab :type fn-cat$c)`, and the overflow table's
length is "kept so the view is the old state exactly"
[fn: books/catalog-paged.lisp:116-143 @3bbfc4dca]. The recorded verdict:
"each stage added a foundation beside the last (D41's "one representation"
became three)" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:175 @worktree].

The third came from the LB lane (catalog columns, `fn-lbc`): the branch "adds
215 books and deletes none" and syncs `fn-lbc` from `fn-cat`, "so it is a
**third catalog representation** beside `fn-cat$c` and `fn-cat-paged`"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:144 @worktree]. Its
own parked continuation states why: "fn-lbc is a standalone defstobj, not an
attachment of fn-cat, so every read arm needs a new fn-lbc argument threaded
through about 50 fn-cat-taking defuns and about 20 proved books, while a
write-side bridge keeps two representations in step. Route A added books and
could delete none until the last reader moved"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:13 @worktree]. And
the bridge had two real bugs the differential found: a catch-up by counts
"cannot tell a cleared-and-regrown catalog from the old one; stale rows
survive", and two withdrawals sharing one version so a sync "skipped the
second" [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:14-16 @worktree].
A third obstacle was ownership: the held row's home is the log, and "A pure
stobj export cannot read the log, so "a columnar concrete of fn-cat" is only
possible by storing the held row in a pool and decoding per call, which IS the
tree codec the cut meant to delete"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:12 @worktree].

## What was done about it

The paged catalog became "the default and only executable catalog" on
2026-10-06 [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:133 @worktree],
and `fn-cat$c` stays as "the correspondence reference, never the generic's
executable foundation" [fn: books/catalog.lisp:1-5 @3bbfc4dca]: still compiled,
still nested, still a field. The M2 plan made LB a third `fn-cat` concrete
behind the attachment (`fn-cat-lbc`) and deletes `catalog-paged.lisp` (3,767
lines), `msgid-linear-exec.lisp` (2,995) and the window forms once LB is the
served path [fn: build/coordinator/CUT-M2-PLAN-20261027.md:68,78-79 @worktree];
the lane parked on 2026-10-28 with the attachment unwritten and its lesson for
fn2: "Decide up front which representation owns the held row; do not keep
two", and "fn2 should have ONE catalog representation from the bottom"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:12-13 @worktree].

## The lesson

Prove a new implementation against the logical object, not against the
previous implementation; a proof by simulation of the old executable keeps
the old executable in the world and, as here, in the state. Introduce a
second implementation as an attachment of the one generic, never as a
standalone stobj threaded beside it. ACL2 states what an attachment shares
and what it replaces: the generic and the implementation have "corresponding
logical skeletons", "each primitive of `gen` has the same logical meaning ...
as the corresponding primitive of `impl`", and "the foundation of `gen`, as
well as execution of the primitives of `gen`, will effectively be provided by
`impl`" [:doc attach-stobj]. And settle ownership before the representation:
a stobj's exports see only the stobj, so data whose home is elsewhere (the
log) cannot be a column of it without a copy.

## The shape to copy

The generic introduced once over its logical side, the implementation chosen
before introduction, every caller compiled against the generic
[fn: books/catalog.lisp:14-22 @3bbfc4dca]:

```lisp
(include-book "catalog-paged")
(attach-stobj fn-cat fn-cat-paged)

(defabsstobj fn-cat
  :foundation fn-cat$c
  :recognizer (fn-cat-p :logic fn-cat$ap :exec fn-cat$cp)
  :creator (create-fn-cat :logic create-fn-cat$a :exec create-fn-cat$c)
  :corr-fn fn-cat$corr-w
  :exports ((fn-cat-count :logic fn-cat$a-count :exec fn-cat$c-count)
            ...))
```

The part not to copy is `:foundation fn-cat$c` living on as a field of the
implementation. A new implementation `fn-cat-X` proves its own correspondence
to `fn-cat$a` (the list) and is attached in place of `fn-cat-paged`; when it
is, the previous implementation's book is deleted in the same landing.
`books/demos/attach-stobj/` in the community books is the manual's worked
example [:doc attach-stobj].
