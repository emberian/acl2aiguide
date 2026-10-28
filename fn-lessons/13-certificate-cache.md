# 13. The certificate cache, poisoned twice

## The wound

fn shares certificates across worktrees and boxes, and its cache has "Two
rules, each paid for by a poisoned cache" [fn: docs/proofs.md:298-299 @3bbfc4dca].
The first poisoning: a certificate lying beside a book was taken as the
book's, but "a `.cert` lying beside a book proves nothing, since after a
merge it can be the previous source's certificate"
[fn: docs/proofs.md:300-302 @3bbfc4dca]. The second: a certificate was keyed
by its own book, but "a certificate is valid only for a book *and every book
it includes*"; "Same book bytes over a changed dependency is a different key,
not a hit ACL2 would then refuse" [fn: docs/proofs.md:308-313 @3bbfc4dca].

Two further costs came from the same cache. A farm box's entries were all
`foreign-local` to every lane, so "a lane's `farm.py submit --closure` onto an
empty remote root re-certified the whole substrate, article and CBOR
dependency set for four new books, half an hour of ACL2 the box had already
run" [fn: docs/proofs.md:376-381 @3bbfc4dca]. And the runner published only
when the whole batch succeeded: "the run certified 21 of 22 books, exited 1,
and left 0 entries" (persvati, 2026-09-20); with per-book publishing "the same
two runs report 21 entries" [fn: docs/proofs.md:403-412 @3bbfc4dca].

## What was done about it

- **Publish only against a manifest.** The runner writes a manifest per run;
  a pair is cached "only when the source beside it still hashes to that run's
  `source_digests_sha256` ... and the certificate beside it still hashes to
  that run's `certificate_digests_sha256`. There is no other publish path, and
  a manifest that did not pass vouches for nothing"
  [fn: docs/proofs.md:302-308 @3bbfc4dca].
- **The key is the closure:** "the SHA-256 of the sorted `<path>:<sha256>`
  listing of the book and its whole local include closure, resolved as ACL2
  resolves `include-book` and ignoring `:dir :system`"
  [fn: docs/proofs.md:309-312 @3bbfc4dca].
- **Content hashes, not dates:** every fn tool sets `ACL2_BOOK_HASH_ALISTP=NIL`
  [fn: docs/proofs.md:295-298 @3bbfc4dca], and the compiled file travels with
  its pair, because "include-book loads it only when it is not older than the
  `.cert`" [fn: docs/proofs.md:351-354 @3bbfc4dca].
- **Per-book seeding:** "A pair is published on its own book's evidence ...
  so a run that is killed, that times out, or that no one waits on still
  leaves what it proved", and publishing refuses a book whose closure no
  longer hashes to what the manifest recorded
  [fn: docs/proofs.md:413-422 @3bbfc4dca].
- The limit is stated: "nothing here proves a book certifies. That is the
  runner's fresh success marker per book, and ACL2 checks the installed pair
  again at include time" [fn: docs/proofs.md:372-374 @3bbfc4dca].

## The lesson

A certificate is evidence about exact bytes: the book's and those of every
book it includes. Key any cache by the whole closure's content, write entries
only from a record of a run that certified those bytes, and never treat a
file's presence as evidence. ACL2's own default fingerprint is weaker than
fn needed: "By default, a book-hash is an alist that records, for a given book
..., its file size (in bytes) and its write-date"; setting
`ACL2_BOOK_HASH_ALISTP` to `NIL` makes it a checksum [:doc book-hash] (chapter
`humans/02-rewriting-theories-books.md` section 2.10.6). Certification refuses
a stale dependency on its own ("An error will occur if `certify-book` has to
deal with any uncertified book other than the one on which it was called")
[:doc certify-book]; a cache that installs a wrong pair converts that refusal
into a confusing one, so the cache must be at least as strict as ACL2.

## The shape to copy

The cache key, as fn defines it [fn: docs/proofs.md:309-312 @3bbfc4dca]:

    key(book) = sha256( sort( [ path ":" sha256(bytes(path))
                                for path in {book} + local-include-closure(book) ] ) )

with the closure resolved as `include-book` resolves it, `:dir :system`
includes excluded, `ACL2_BOOK_HASH_ALISTP=NIL` in the environment of every
ACL2 that certifies, and a write path that accepts a pair only together with
the manifest of the run that produced it.
