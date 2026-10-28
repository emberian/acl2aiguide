# Lane D: fn-lessons, by wound

Read `/Users/ember/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `fn-lessons/README.md` (one paragraph on what fn was and why it is being
  rebuilt; the list of lessons with one line each)
- `fn-lessons/NN-<wound>.md`, one file per wound (expect 12 to 20)

## What a lesson is

A wound is a thing fn paid for: a defect, a quadratic path, a proof that
took forty minutes doing two hundredths of a second of proving, a
representation asked for six times and never made the only path, a lane
that measured nothing because it hit a step limit, a lock scheme that was
two schemes, a twin forest of 361 copied books, an apparatus a third the
size of the host it checked. Each lesson file has, in this order:

1. **The wound**, in one paragraph, with the measurement (the number, the
   date, the box) and the fn path and sha that shows it (`[fn: PATH:LINE
   @SHA]`; `origin/dev` is `3bbfc4dca`; use `git -C /Users/ember/dev/fn log
   --all -S'<text>'` and `git -C /Users/ember/dev/fn show SHA:PATH` to pin an
   older sha when the wound is in history, and `cv search` / `cv show` for
   the episode, cited `[cv: ID#N]`).
2. **What was done about it** in fn (the tool, the macro, the ruling, the
   deletion), with its path.
3. **The lesson**, stated as a rule a fn2 builder or any ACL2 project can
   follow, in two or three sentences, with the ACL2 mechanism it rests on
   cited to the manual (`[:doc TOPIC]`).
4. **The shape to copy** when there is one (a form, a book layout, a
   command), whole.

Ember's own words, when they name the wound, are quoted verbatim from
`EMBER.md` with the citation it gives.

## The wounds to cover (start here; add what you find)

Read first, whole: `ANATOMY-20261009.md` (the three sins),
`REPRESENTATION-HISTORY-20261028.md`, `PROCESS-AUDIT-20261009.md`,
`AUDIT-TWO-WEEKS-20261013.md`, `RULINGS.md`, `EMBER.md` sections "Cut,
drain, collapse", "Assurance", "Process and cycle time", "Coordination and
seats", `CUT-M2-PLAN-20261027.md`, `lanedumps/cut-m2a-lb-continuation.md`,
and fn `docs/proof-style.md` and `docs/proofs.md` (both carry measured
wounds with dates). All under `/Users/ember/dev/fn/build/coordinator/` and
`/Users/ember/dev/fn/docs/`.

- Octet lists at runtime: asked for six times (REPRESENTATION-HISTORY
  table), landed as twins beside the list paths, `fnn-octet-list` calls
  130 to 263; the law that produced twins (D27's "correspondence theorem to
  the list definition at every boundary") vs the law that would not have
  ("the derived path is the ONLY path", `/Users/ember/dev/minidregg/CLAUDE.md`).
- Conceptual multiplication: ladders of rungs (history 120 books, bp-node
  60, catalog 28 + 4.5K + 3.3K lines, three msgid representations), 766
  functions car/cdr-walking octet data, a 3 MiB POST changing
  representation seven times (ANATOMY sin 1).
- The host decides: 620 host functions branching on policy, 163 mutex sites
  in owner.lisp, two lock schemes that cannot see each other
  (docs/proofs.md "One lock per box") (ANATOMY sin 2).
- The apparatus outgrew the organism: 301K lines of registers, 45K of
  checkers, 130K of tests, 55K of planning (ANATOMY sin 3; AUDIT-TWO-WEEKS
  section c).
- Whole-state recognizers on the served path (`fn-statep` Theta(n^2) on
  every operation; docs/proof-style.md section 4).
- Exported internals: 806 raw-list accessors, 642 `-is-`/`-of-` equalities
  as global rewrite rules, 116 reaches for `minimal-theory`, 668M of 1.50G
  frames useless (docs/proof-style.md top and section 8).
- The `Time:` line: 2,386 s with 0.02 s of proving (docs/proof-style.md 9.1)
  and the `Goal` `:in-theory` that did not survive a subgoal (9.3: 609 s to
  6.5 s).
- Step-limited probes that measured nothing (9.2).
- A `:linear` + `:rewrite` rule crashing SBCL; arithmetic-5 ten times slower
  than fixed-modulus lemmas (docs/proof-style.md last lines).
- The certificate cache poisoned twice (docs/proofs.md "Certificates": a
  `.cert` beside a book proves nothing after a merge; the key is the closure).
- `git log` read as green for a day (docs/proofs.md green_check, F4).
- Triage: one closure run names one layer of reds; 39 runs and 9 hours
  (docs/proofs.md "when the closure is red").
- `defabsstobj` by hand: 285 obligation blocks, 5,800 lines, catalog.lisp
  2,595 (cv search 'GENERATORS' lane ac7362ee; the generator that replaced
  them); the paged catalog nesting the old foundation whole
  (catalog-paged.lisp header) and the LB columns becoming a THIRD catalog
  (REPRESENTATION-HISTORY 3.2).
- `with-local-stobj`'s return shape and the REPL refusing to redefine
  (lanedump "How to run").
- The twin forest: 361 books copied to make events `local` (RULINGS
  2026-10-15).
- Foreground waits: 32% of seat wall-clock; status censuses; summary-based
  restarts (PROCESS-AUDIT).
- Proof-first vs semantics-first: ember's "sometimes we shouldn't do those
  at the same time"; representations designed for the proof (EMBER.md,
  ANATOMY).
- The crash model: what `byte-store.lisp` models, what it does not
  (REPRESENTATION-HISTORY "a specification, by design"; ember 2026-10-28
  "we're not convinced that our crash model is actually an appropriate
  model"), as a lesson about modelling the OS.
- fn's `def-loop`: 850 identical inductions tree-wide before one bridge per
  shape (def-loop.lisp header) as the positive lesson about functional
  instantiation.
- Teeth: the false OB-2 that passed a polarity-only audit (`cv search
  'OB-2'`; minidregg memory says 2026-08-07) and the general negated
  `must-fail` that proves nothing (docs/proof-style.md section 5).

## Report

READY with the file list, the sources block and the README lines; or
BLOCKED. Every number in a lesson is either quoted from a source with the
citation or re-measured by you with `[measured: COMMAND]`.
