# acl2aiguide: continuation (present state; rewritten whole)

Coordinator brief: `/Users/ember/dev/fn/build/coordinator/briefs/ACL2AIGUIDE-20261028.md`.
Lane briefs: `coordination/COMMON.md` (every lane), `coordination/LANE-*.md`.
Rules: `WRITING.md`. Toolchain: `sources.md` "Toolchain".

## State

- Skeleton committed (`4d297e4`): README, WRITING, sources, examples
  harness (`examples/certify.sh`, mkdir lock, `cert.pl` with the laptop
  ACL2 8.7), briefs A/B/C.
- Wave 1 running: Lane A (humans/01, 02 + examples/prover, rewriting,
  books), Lane B (humans/03, 04 + examples/modelling, stobjs, systems),
  Lane C (humans/05, 06 + examples/performance, process). Opus, spawned
  2026-10-28 ~01:05 EDT.
- Wave 2 briefs written, not launched: Lane D (`fn-lessons/`), Lane E
  (`ai/00`, `01`, `02` + examples/shapes). Lane F (`ai/03`..`06`: the terse
  twins of humans/01..06, written from part 1 once it exists) is not yet
  briefed.

## Next

1. On each wave-1 READY: read the chapter whole; check every `[:doc]`
   against `acl2-doc.lisp` (grep the topic name), spot-check obligations
   against the manual's text, re-run `examples/certify.sh` on the lane's
   examples, fold the sources block into `sources.md` and the README line
   into `README.md`, commit the lane's named files. Send the lane back for
   any claim without a source or any example that does not certify.
2. When wave 1 is merged: report READY (part 1 first complete draft) to
   main; launch D and E together, then F.
3. Examples milestone: `make -C examples` green from clean (`make clean`
   first) is the "examples certified" READY.
4. Park here with this file rewritten whole.
