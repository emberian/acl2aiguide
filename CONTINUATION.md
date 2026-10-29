# acl2aiguide: continuation (present state; rewritten whole)

Coordinator brief: `~/dev/fn/build/coordinator/briefs/ACL2AIGUIDE-20261028.md`.
Lane briefs: `coordination/COMMON.md` (every lane), `coordination/LANE-*.md`.
Rules: `WRITING.md`. Toolchain: `sources.md` "Toolchain". Public at
`github.com/emberian/acl2aiguide`; push `main` after every merge; no
secrets, no absolute machine paths (sweep `/Users/ember` and `/private/tmp`
out of every new file before committing).

## State (2026-10-29)

Parts 1 and 2, `fn-lessons/`, and their examples: unchanged since
2026-10-28 (see git history for that state's account).

**Part 3, `assured/` ("a framework for assured TigerStyle with ACL2"),
first complete draft**, written from fn2's working instance:
`assured/README.md`, seven humans chapters (`assured/humans/01`..`07`:
rules as declarations; simulation and checkers; commuting squares;
certify cost; transport; the metatheory split; honest costs) and their
seven agent twins (`assured/ai/01`..`07`). Pinned sources: fn2 books on
`origin/fn2/main` `127f7b877`, Lean on `origin/fn2/lean-meta` `dddc32d34`,
coordinator documents read 2026-10-29 (`sources.md`, "fn2 (part 3)").

**Examples certified**: 12 new books in `examples/assured/`
(`README.md` maps them to chapters); all 107 books under `examples/`
certify from clean with `make -C examples clean && make -C examples`
(laptop, ACL2 8.7 / SBCL 2.6.8, one certification at a time, 2026-10-29).

How part 3 was written: the coordinator wrote the 12 examples and humans
01 and 04; Astra (`codex exec -m gpt-6-astra -s read-only`) drafted
humans 02, 03, 05, 06, 07 and all seven ai twins from briefs naming the
sources; the coordinator reviewed each against the sources (manual quotes
grepped in `acl2-doc.lisp` and community-book docs; fn2 and Lean line
citations opened at the pinned shas; paperbin filenames checked) and
replaced the drafts' placeholder example text with what the certified
books actually assert. No Opus writer was spawned.

Findings made while writing, now in the text:
- The step counter does not track the per-array NTH family's cost: at 36
  fields the generic proof takes a hundred times the specific one's time
  for about twice the steps (`assured/humans/04` 4.3, `sources.md`).
- `examples/assured/owed.lisp`'s owed row `sat-run-monotone` is false at
  x = 256 (Astra found it; now proved in the book as
  `sat-run-monotone-false-at-256`): a certified ledger can hold a false
  conjecture with passing teeth (`assured/humans/07` 7.2).
- `timeout` (SIGTERM) does not stop an SBCL ACL2 driver; use
  `timeout -s KILL` (`sources.md` "Measurements").

## Known gaps (not blockers)

- `assured/ai/*` twins were drafted by Astra from the finished humans
  chapters and spot-checked, not read line by line by the coordinator.
- `examples/assured/sim.lisp`'s replay assertion compares two identical
  calls; it does not pin a stored fingerprint across edits.
- No example isolates WORK-style independent accounting, a process driver
  that fails on missing execution, or a generator-mode (paired replay)
  checker; chapter 2 cites fn2's forms for these.
- `summary-upto.lisp` instantiates the parity counter, not read-state
  (HIGHER-STRUCTURES section 6 proposed re-instantiating read-state).
- The new citation forms `[guide: PATH:LINE]` and
  `[fn: commit message of SHA]` were added to `WRITING.md` for part 3.
- Earlier gaps stand: GL/FGL, ATC, APT (beyond `propagate-iso`), FTY,
  `std/io` shown by their own tests; `xdoc::save` has no recipe; the
  `attach-stobj` one-book failure may be worth reporting upstream.

## Next, if resumed

1. A coordinator line-by-line pass over `assured/ai/*` against their
   humans chapters.
2. Refresh part 3 when fn2 moves: the owed counts, the stop-reason enum
   and the generator line numbers are pinned to `127f7b877`.
3. Add the missing examples above if a reader asks for them.
