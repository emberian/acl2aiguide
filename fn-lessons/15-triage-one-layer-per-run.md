# 15. Triage: one closure run names one layer of reds

## The wound

"`include-book` refuses an uncertified dependency, so a closure run stops at
the first failure and every book above it reads "There is no certificate on
file": one run names one *layer* of independent reds, and a ten-deep chain
costs ten runs -- the shape that took three lanes, thirty-nine runs and nine
hours on 2026-09-22" [fn: docs/proofs.md:556-560 @3bbfc4dca]. The same day a
second misreading added four hours: a finished lane was held because a
dependent was "already red for a reason the branch did not cause", which
"held a finished lane for four hours and added nothing, since its own books
had certified inside the lane" [fn: docs/proofs.md:475-478 @3bbfc4dca].

## What was done about it

`tools/triage.py` runs ACL2's provisional certification instead of an
ordinary closure: a Create wave that skips proofs, "**one parallel Convert
wave that does every book's proofs** -- Convert takes a sub-book's `.pcert0`
in place of a certificate, so the proofs are not a chain", and a Complete
wave. Each failed book is then classified: an independent red, a timeout,
*blocked* ("its Convert PASSED, so every proof in it succeeded, and a book
below it has no certificate -- nothing hides behind such a book"), a cascade
(a Create failure, "the one kind that can still hide another book's
proofs"), or unexplained. On a 63-book closure at 8 jobs, "an ordinary round
took 690.8 s and named one independent red with fifteen books cascading
behind it; one provisional round took 317.3 s and named four independent reds
and twelve proved-but-blocked books with nothing unanswered"
[fn: docs/proofs.md:561-579 @3bbfc4dca]. Its result is never a certificate:
"**A triage run is evidence of nothing but its list of reds**", run with
`--no-publish`, its manifest not archived, its report naming no certify run
id [fn: docs/proofs.md:588-596 @3bbfc4dca]. And root's procedure runs "one
provisional wave (`tools/triage.py`) over the image closure per batch of
merges, comparing red sets and forms with the previous wave's. A new red
belongs to that batch and is fixed before the next merge"
[fn: docs/proofs.md:473-475 @3bbfc4dca].

## The lesson

When a closure is red, find all of its reds in one run: provisional
certification exists "to break sequential dependencies caused by
`include-book`" [:doc provisional-certification] (chapter
`humans/02-rewriting-theories-books.md` section 2.10.7). Treat what it
produces as a diagnosis only, because "for maximum trust, it is best for all
books in a project to be certified from scratch without the provisional
certification process" [:doc provisional-certification]. Attribute a red to
the change that caused it by comparing red sets between waves, not by holding
work that did not cause it.

## The shape to copy

The community build tool runs the three waves itself; the manual's form is
`cert.pl --pcert-all -j 4` over the targets [:doc provisional-certification].
fn's wrapper adds the classification above and refuses to publish anything
from the run [fn: docs/proofs.md:588-592 @3bbfc4dca]. One more instrument fn
tried and found weak: substituting a book's last green source into the remote
tree, which "failed on a *different* theorem, because those bytes were green
over dependencies this tree no longer has" [fn: docs/proofs.md:581-588 @3bbfc4dca].
