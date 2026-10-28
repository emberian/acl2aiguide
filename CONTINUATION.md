# acl2aiguide: continuation (present state; rewritten whole)

Coordinator brief: `~/dev/fn/build/coordinator/briefs/ACL2AIGUIDE-20261028.md`.
Lane briefs: `coordination/COMMON.md` (every lane), `coordination/LANE-*.md`.
Rules: `WRITING.md`. Toolchain: `sources.md` "Toolchain". Public at
`github.com/emberian/acl2aiguide`; push `main` after every merge; no
secrets, no absolute machine paths (sweep `/Users/ember` and `/private/tmp`
out of every new file before committing).

## State (2026-10-28)

All three milestones reached and pushed:

- **Part 1 first complete draft**: `humans/01`..`06` (prover and rewriting;
  modelling data and systems; performance; process).
- **Part 2 first complete draft**: `ai/00` (pitfalls first, ranked from the
  transcripts), `ai/01` (form shapes), `ai/02` (reading the manual, ACL2 as
  a tool), `ai/03`..`06` (the terse twins of part 1 plus running ACL2 from
  an agent).
- **fn-lessons**: README plus 23 wounds.
- **Examples certified**: 86 books under `examples/` certify from clean with
  `make -C examples clean && make -C examples` (cert.pl, laptop ACL2 8.7 /
  SBCL 2.6.8, `ACL2_BOOK_HASH_ALISTP=NIL`, one certification at a time).

Every chapter was reviewed by the coordinator against the manual: every
`[:doc]` topic grepped in `books/system/doc/acl2-doc.lisp` (or the
community book named), quoted phrases spot-checked against the source,
every cited paper confirmed in `~/paperbin`, several transcript citations
opened. Three claims were settled by measurement during review and recorded
in `sources.md` "Measurements": the comment-edit book-hash question, the
`:linear` memory fault, the `defabsstobj` one-book `attach-stobj` failure
(Lane B's). `README.md` and `sources.md` are current.

## Known gaps (not blockers)

- GL/FGL, ATC, APT, FTY and `std/io` are shown through the community books'
  own tests; they are not certified on the laptop (closures too long).
- `xdoc::save` has no recipe (not run here).
- The `attach-stobj` one-book failure ("This is supposed to be impossible",
  humans/03 3.10) may be worth reporting upstream.
- Chapter line counts: `ai/03` and `ai/04` run over the brief's 700-line
  target because each condenses two humans chapters.
- `fn-lessons` cites `ad44eec2#263` for the false OB-2 (a Lean episode).

## Next, if resumed

1. A second-pass audit by a fresh reader of one chapter at a time against
   the manual, looking for paraphrased obligations that should be quotes.
2. Trim `ai/03` and `ai/04` toward 700 lines if an agent-context budget
   asks for it; keep every form.
3. If ember wants GL/FGL or ATC examples certified, do it on a box with
   those closures built, never on the laptop.
