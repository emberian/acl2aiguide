# 06. The apparatus outgrew the organism

## The wound

At the freeze fn was "About 1.47M lines to ship 108K lines of logic and 81K
of host": 721K lines of books, 81K of host, 301K lines of generated planning
JSON committed to git ("256 of 3,908 October commits only regenerate them"),
131K lines of Python tools of which "checkers and gates 45K in 54 files", 130K
lines of Python tests, 55K lines of planning markdown
[fn: build/coordinator/ANATOMY-20261009.md:7-18 @worktree]. ANATOMY's third
sin: "301K lines of registers, 45K of checkers, 130K of tests and 55K of
planning prose exist so many agents could work without colliding. The
checkers are a third again the size of the host they check"
[fn: build/coordinator/ANATOMY-20261009.md:28 @worktree].

It kept growing after the freeze. "Since the freeze, 110 of the 175 lane
merges (63%) are `b-` (tools, trains) or `d-` (burndown, registers) lanes.
tools grew 155.9K -> 166.4K lines and tests 544.6K -> 571.4K, against 2 `post`
and 3 `over` lane merges. The train is now at "17 gates""; the coordinator's
own account: "the tools and tests keep growing because every gate I rule into
existence is Python with a unit test"
[fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:50 @worktree]. Ember had
asked for the opposite: "lets NOT BE EXECUTING ALL OF THIS EVERY TIME. we
need to be building things so we cand o the least amount of work to iterate on
exactly and only what is red and not be revalidating things that are slow"
[fn: build/coordinator/EMBER.md:697-699 @worktree] [cv: be1e9dcf#883];
""evidence archive" why are doing all this rituals about "evidence." deep down
you know it's just cargo culted bullshit"
[fn: build/coordinator/EMBER.md:719 @worktree] [cv: be1e9dcf#6393]; and on
2026-10-17, looking at checkers running at 85-100% CPU: "we are overloading
this machine we are developing on with some major bullshit that doesn't
actually inform us :)" [fn: build/coordinator/EMBER.md:383-385 @worktree].

Part of the Python exists because it mirrors ACL2. `tools/ledger.py` re-reads
the books with its own reader, so "Editing `fn-defrecord` means editing two
files ... because a static reader cannot see through a macro"
[fn: docs/proof-style.md:142-149 @3bbfc4dca], and the inventory counted
"three Python police" beside 3,272 hand `must-fail`s
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:26 @worktree].

## What was done about it

The surgery plan put "The apparatus with the coordination rewrite: registers
regenerated into `build/`, one checker per contract, ratchets compared against
the last qualified artifact" last [fn: build/coordinator/ANATOMY-20261009.md:80 @worktree].
What shrank in the two weeks after the freeze was "only the generated planning
registers (-63.7K lines leaving git)" [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:71 @worktree].
The M2 cut stopped taking the apparatus from lanes: "Not taken from any lane
(anti-groove, M1-d): `build/**` ..., `planning/**` registers and evidence ...,
`tools/` apparatus edits whose tool M1-d deletes"; in a merge "the deletion
wins" [fn: build/coordinator/CUT-M2-PLAN-20261027.md:15 @worktree]. The
generators started writing what they generated into the world: `def-loop`
emits "a row in the world table `fn-generated` naming what was generated, so a
tool reads the world rather than a mirror of this macro"
[fn: books/def-loop.lisp:62-64 @3bbfc4dca].

## The lesson

A check that a fact holds of the ACL2 world belongs in the world, as an event
that fails certification, and not in a program that re-parses the books
beside it. `make-event` is the mechanism: "the expression `(make-event form)`
replaces itself with the result of evaluating `form`", and the form may read
the world [:doc make-event]; a generator can record what it produced in a
`table` that a later event reads [:doc table]. Count the apparatus as part of
the system's size, and require each checker to name the contract it enforces
and the defect class it has found; a checker with neither is deleted.

## The shape to copy

`books/definterface.lisp` is fn's own model of the right shape: "one form per
host-called entry, checked against the loaded world by `make-event`"
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:185-186 @worktree].
A small check of the same kind, refusing certification unless a fact about
the world holds, is in this guide's examples
[example: examples/books/make-event-check.lisp] (chapter
`humans/02-rewriting-theories-books.md` section 2.10.8).
