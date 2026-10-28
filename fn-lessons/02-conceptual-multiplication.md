# 02. Conceptual multiplication: ladders of rungs, and a POST that changes representation eighteen times

## The wound

ANATOMY's first sin, measured on the freeze tree (dev `3a937ebc3`,
2026-10-09): "Every storage concept is a ladder of rungs, each reified as
books with their own invariants, cursors, census and refinement: history 120
books (59 with executable code, spread one to 26 functions each); bp-node 60
books; catalog 28 plus a 4.5K-line logic book and a 3.3K-line paged book;
msgid 12 books over three representations with exec twins. The owner is a
sprawl rather than a ladder: 162 books, 1,144 executable functions, 14
subfamilies. 766 executable functions car/cdr-walk octet-typed data despite
D27; a 3 MiB POST changes representation about seven times between socket and
log" [fn: build/coordinator/ANATOMY-20261009.md:26 @worktree]. The proof
volume was not the sin: about 6:1 proof to definition, against seL4's about
20:1 [fn: build/coordinator/ANATOMY-20261009.md:18 @worktree].

Re-traced at `origin/dev`, the POST count was an undercount: "**POST, socket
to log: 18 whole-article representation changes, 16 under the owner mutex**"
-- a fresh vector, the octet buffer, 512-octet packed bignum blocks, a list of
line lists, one flat cons list, one bignum at enqueue, a list again at take, a
vector, the buffer again, a list for the article record, an arena page, "the
same list as step 10, built again", a CBOR record list with a 15-way `append`,
a vector, a list twice more, a framed entry list, a vector for `write(2)`;
"at least about 14 whole-article cons-list passes at 16 B/octet"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:89-110 @worktree].
Two of those representations (packed-submission and body-chunks) were added
three days after D27 [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:131 @worktree].
The read path, by contrast, is "3 whole-article copies, all buffer to buffer,
no octet list" [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:112 @worktree].
The 766 count was re-measured as a smell, not a count of octet loops: most of
the listness "sits in untyped record and alist plumbing"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:68 @worktree].

Ember, the night the collapse was named: "do we need to just ... "collapse the
ladders" ?" [fn: build/coordinator/EMBER.md:275 @worktree] [cv: 35f3668a#1377],
and "we definitely need to be simplifying and reducing duplication and
unnecessary conceptual multiplication; just because we expect to have a lot
of proof per logic doesn't mean we need to go about it foolishly. in fact, the
task is SO challenging that unless we go about it quite intelligently, we will
literally never finish it :)" [fn: build/coordinator/EMBER.md:283 @worktree]
[cv: 35f3668a#1466].

## What was done about it

Little, and the tree grew. In the four days after the freeze "books grew by
55 files and 59.7K lines, and none of the five collapse-list families shrank"
(history 136 to 138 books, owner 188 to 190, msgid/index 100 to 99, bp 237 to
237, post 59 to 66) [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:34,72 @worktree].
The collapse was gated behind "the vertical path naming its survivors" and
moved to "post-horizon" [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:20-21 @worktree].
The M2 plan of 2026-10-27 leaves "The history ladder rungs, the three
Message-ID representations and the owner's 14 subfamilies" to a later cut
[fn: build/coordinator/CUT-M2-PLAN-20261027.md:188 @worktree], and the
2026-10-28 decision rebuilds bottom-up as fn2
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:3 @worktree].
What the record proposes to settle first is one value with one owner: "What
*is* an article's bytes, as one value with one owner, from the socket read to
the log write? ... Every divergence above follows from leaving this open: each
layer (wire scan, injection, queue, record codec, log kernel) picked its own
carrier, and the correspondence-twin discipline made each choice locally
provable and globally additive"
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:183 @worktree].

## The lesson

Decide, before the first layer is written, which representation each datum
has and which layer owns it, and make every later layer consume that
representation rather than choose its own carrier. A rung that refines the
one below it is a proof obligation, not a new data structure: keep the
refinement in the logic and keep one concrete foundation per logical object.
ACL2's mechanism for "one logical object, a choice of concrete
implementations" is the attachable abstract stobj, where "each primitive of
`gen` has the same logical meaning (i.e., the same `:logic` function) as the
corresponding primitive of `impl`" and the implementation is chosen by
`attach-stobj` [:doc attach-stobj]; its authors built it so that "different
ACL2 sessions can specify different ways to execute operations on ST without
the need to recertify the book that defines ST"
[paper: kaufmann2025-acl2-mutable-objects-several-implementations.txt, section 2].
Single-threadedness then gives the bytes one owner: a stobj formal accepts
only "the variable `OBJ`, not merely a term that ``evaluates to an obj''"
[:doc stobj].

## The shape to copy

A table, written before any book, with one row per datum and three columns:
its representation (one), the layer that owns it (one), the layers that read
it and through which export. fn's own version of the table, at the end of the
investigation, is the model: per data kind, what ember asked for, what dev
has, and where it diverged
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:167-181 @worktree].
A row with two representations is a defect before it is a design. For the
mechanics of a generic with an attached implementation, read the community
demo the manual points to, `books/demos/attach-stobj/README.txt`
[:doc attach-stobj], and fn's use of it, `books/catalog.lisp:14-17`
[fn: books/catalog.lisp:14-17 @3bbfc4dca]; lesson 03 is what went wrong next
to it.
