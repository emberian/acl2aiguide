# Lane F: part 2 for AIs, the terse chapters

Read `~/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `ai/03-prover.md` (the terse twin of humans/01 and 02)
- `ai/04-modelling.md` (the terse twin of humans/03 and 04)
- `ai/05-performance.md` (the terse twin of humans/05)
- `ai/06-process-and-repl.md` (the terse twin of humans/06, plus running
  ACL2 from an agent: one session, certify a changed book yourself, host
  and cache pitfalls, batching over one-statement loops)

## Method

Read `humans/01` to `humans/06` whole (they are the sourced, reviewed
text), `ai/00-pitfalls-first.md` and `ai/01-form-shapes.md` (Lane E's),
and `fn-lessons/README.md`. Each `ai/` chapter is written to be loaded
whole into an agent's context before it works in ACL2: terse, imperative,
example-dense, pitfalls first. Per topic: one line of what it is; the
pitfall and how it prints; the shape to copy (a form, whole, from
`examples/`); the rule; the source line. No narrative, no history except
one line when a wound is the reason for a rule. Target 300 to 700 lines
per chapter. Every `[:doc]`, `[fn:]`, `[example:]` citation is carried
over from the humans chapter it condenses or verified by you; add nothing
the humans chapters and the manual do not support. Where the humans
chapter is wrong against the manual, say so in your report (do not fix
the humans chapter; the coordinator does).

`ai/06` adds, from fn `docs/proofs.md` "proof work gets a live session",
`docs/proof-style.md` 9.x, the lane continuation's "How to run", and
`EMBER.md` 2026-10-27 ("iterating across the whole system and using mental
simulations ... without wasteful rerun loops"): the one-session rule; the
driver-file batch (`timeout N acl2 < driver.lsp > out 2>&1`, read once);
`(set-gag-mode :goals)`; `with-prover-time-limit` on every form; certify
the changed book with `cert.pl` before reporting; what a certificate
covers (`ACL2_BOOK_HASH_ALISTP=NIL`, closure key); the REPL refusing to
redefine (restart after an edit); background anything over 100 s with a
PID file, never a foreground sleep; never a status census; resume the
agent that holds the context rather than restarting from a summary.

## Report

READY with the four chapters, the sources block, the README lines, and any
disagreement you found between a humans chapter and the manual; or
BLOCKED.
