# 07. Certified, and reached by no host build

## The wound

At the freeze, 1,352 books (556K lines) were in the execution graph; of the
565 that were not, 342 were reached only by test or tool fixtures, 68 named a
claim, and "71 (15K) are retire candidates (executable rungs no claim names,
legacy readers, D46-unhooked)" [fn: build/coordinator/ANATOMY-20261009.md:22 @worktree].
The certify economics followed: "1,917 books, 565 of them certified for no
image" [fn: build/coordinator/ANATOMY-20261009.md:63 @worktree].

The four landings the M2 cut was built around had the same shape at full
scale: "**The one fact that reshapes M2: none of LB, LC, landing 2 or LA
touches the host.** [M] LB adds 0 host lines, LC adds 0, landing 2 adds 1 ...
The "new path becomes THE path" work (the attach, the host entry points, the
open) was never written; it is M2's real work, not a merge. The seats'
certified/stack-point status certifies proof books that no host build
reaches" [fn: build/coordinator/CUT-M2-PLAN-20261027.md:11 @worktree]. Of LB's
additions, "[M] 28.1K are LB proof books no host build reaches"
[fn: build/coordinator/CUT-M2-PLAN-20261027.md:186 @worktree]; LC's "proved
fn-pck machine "is on no executable path today""
[fn: build/coordinator/CUT-M2-PLAN-20261027.md:105 @worktree]. And because the
M1 cut deleted unreached books by a reach rule, it deleted books the unmerged
landings included: about 8.4K lines for landing 2 and 4.7K more for OVER
"must come back" [fn: build/coordinator/CUT-M2-PLAN-20261027.md:12 @worktree].
Earlier, M1 had deleted "concrete paths **built and never wired**": cached NOV
row references, catalog column facts across the host protocol, the
incremental history page reader [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:151-159 @worktree].

Ember asked the question on 2026-10-10: "uhhh "why are we extracting so much"
like so much of the acl2 definitions have gotta be useful only for the proofs
right? like whats the actual formal symbolic critical path thru...."
[fn: build/coordinator/EMBER.md:317 @worktree] [cv: 905fe751#2886].

## What was done about it

- The rule (GPT-6, 2026-10-09): "every maintained book belongs to the
  execution, assurance or qualification closure of a named supported claim,
  or is explicitly parked" [fn: build/coordinator/ANATOMY-20261009.md:22 @worktree].
- fn's proof registry already had the subject rule: "Where a cited theorem is
  about a function the host does not call, the entry carries a
  `pending_subject` note saying so; the citation stands as component evidence
  and does not meet the subject rule until a theorem equates the two
  functions" [fn: docs/proofs.md:862-865 @3bbfc4dca], and its strategy said
  "The program used by the host must be these definitions or a justified
  refinement. An abstract model plus an independently written server is
  insufficient evidence for claims about the running server"
  [fn: docs/proofs.md:59-61 @3bbfc4dca].
- M2 named the wiring of each landing as the work and gave every path a gate
  that builds the images and runs the native tests of the families it touches
  [fn: build/coordinator/CUT-M2-PLAN-20261027.md:14,212-214 @worktree]. It
  parked on 2026-10-28 with that wiring unwritten
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:3-5 @worktree].

## The lesson

A theorem is evidence about the running system only when its subject is a
function the host calls, so a landing is the wiring: the host entry calls the
new definition, the old path is deleted, and the proof books ride in the same
commit. Measure reach from the host's build files through `include-book`
closures; a book outside every claim's closure is deleted or parked by name,
never certified "for later". Certification does not establish reach: its
dependency rule is only that "An error will occur if `certify-book` has to
deal with any uncertified book other than the one on which it was called"
[:doc certify-book], which says nothing about who calls what.

## The shape to copy

One gate per landing that cannot pass without the host: the M2 gate builds
the four images and runs the native tests matched to the families the path
touches, and "The certified/stack-point status of the lanes is information,
not a gate" [fn: build/coordinator/CUT-M2-PLAN-20261027.md:212-224 @worktree].
Beside it, the registry's subject rule above, stated per keystone: the
function its statement is about, and the host entry that calls that function.
