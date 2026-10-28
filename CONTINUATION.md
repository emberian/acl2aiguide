# acl2aiguide: continuation (present state; rewritten whole)

Coordinator brief: `/Users/ember/dev/fn/build/coordinator/briefs/ACL2AIGUIDE-20261028.md`.
Lane briefs: `coordination/COMMON.md` (every lane), `coordination/LANE-*.md`.
Rules: `WRITING.md`. Toolchain: `sources.md` "Toolchain".

## State

- MILESTONE: part 1 first complete draft (humans/01..06, 67 certified
  examples) merged at `985c188`. Lanes A (`ce2c34b`), C (`8ccff03`), B
  (`985c188`) reviewed against the manual (every [:doc] topic grepped in
  acl2-doc.lisp; quoted phrases spot-checked; papers checked in ~/paperbin).
- Running (Opus, three at a time): Lane D (fn-lessons/; spawned ~02:00
  EDT), Lane E (ai/00, 01, 02 + examples/shapes; ~02:55), Lane F (ai/03..06;
  ~03:50).
- Owed: the "examples certified" milestone = `make -C examples clean && make
  -C examples` green from clean after every lane's examples are in.

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
