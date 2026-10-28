# 19. Foreground waits, status censuses and summary restarts

## The wound

The process audit of the rewrite's first day (2026-10-09, 25 sub-agents):
"Waiting took 10.7% of tokens (target under 10%) and 32% of seat wall-clock,
nearly all of it the integrator's foreground `until` loops (Builder B: 5.4 h
of 10.4 h)" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:3 @worktree].
"B1 and B2 spent 5.4 h of 10.4 h in 77 calls over 60 s (most of them `until
grep ... ; do sleep 15` loops moved to the background at the 600 s timeout),
and 81.5M tokens went to poll turns. A1 and C1 used Monitor (50 and 31 calls)
and spent 0.04 h and 0 h waiting"; and a waiting seat is deaf: "8 of them
arrived while B1 or B2 sat in a foreground wait, queued 0.1 to 5 min"
[fn: build/coordinator/PROCESS-AUDIT-20261009.md:57,66 @worktree]. Opus
builders ran to 790k context at 120M to 130M tokens an hour
[fn: build/coordinator/PROCESS-AUDIT-20261009.md:69-70 @worktree].

Over the two weeks: "157 seat spawns across 8 seat lines"; "POST landing 2"
alone "was briefed to seven consecutive P seats (P7-P13) in 38 hours"; 418
sub-agents "ended on a "ceiling/continuation/park" line"
[fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:52 @worktree]. Ember named
both patterns on 2026-10-04: "you need to stop using these prompts as an
opportunity to do an auditcensus. we've already done plenty of censuses ...
we send out one agent to gather context, and once it has done all the hard
work of building the context ,we have it emit a lossy summarization that
doesn't make sense without the grounding context and ship that over to a
separate agent to do the implementation. that is foolish and stupid. we
oughta be empowering these guys and then sending them back quests once they
are leveledup with their context" [fn: build/coordinator/EMBER.md:835 @worktree]
[cv: 9627d694#2912]. And on cycle time: "earlier in this project we were
doing LIVE QUALIFICATION IN THE REPL and even outside the repl like FIVE
MINUTE CYCLES so something seems wretchedly disgustingly bad right now"
[fn: build/coordinator/EMBER.md:735 @worktree] [cv: 905fe751#4541].

## What was done about it

- Two of the day's targets held: "zero status messages" (49 messages to the
  coordinator, all READY, BLOCKED, DECISION, RED or park notices) and "zero
  fresh-agent restarts of a live concept" (five successions, "each from the
  predecessor's own continuation file")
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:12-13 @worktree].
- The integrator's brief replaced "every `until`/`sleep` loop with a
  background `train.py certify` plus a Monitor on its log", with a `--notify`
  line to match [fn: build/coordinator/PROCESS-AUDIT-20261009.md:67 @worktree];
  builders park at 400k context instead of 790k
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:71 @worktree].
- The M2 seat briefs: "read all of the path's sites first, make the edits as
  one coherent set, run only sub-minute laptop checks ..., then the one gate",
  with no status censuses and verification once at the end
  [fn: build/coordinator/CUT-M2-PLAN-20261027.md:199 @worktree].

## The lesson

Never block a working session on a long job: start it detached, have it emit
one line on completion, and keep working; a seat that waits in the foreground
is deaf to every message meanwhile. Agents report on events (ready, red,
blocked, a decision needed) and never on a schedule. The agent that built the
context does the next piece of work in it; a successor starts from that
agent's own continuation file, not from a summary written by someone else.
The fast inner loop is the REPL, "The ACL2 read-eval-print loop, file
loader, and command processor" [:doc ld], with each proof attempt wrapped in
`with-prover-time-limit` so that a search that does not return is aborted at
its limit [:doc with-prover-time-limit]; that is how fn's
proof sessions reached "seconds per attempt against cached certificates"
[fn: docs/proofs.md:503-505 @3bbfc4dca].

## The shape to copy

The audit's own measure is the shape: per seat, the share of wall-clock
spent inside blocking calls over 60 s, and the share of tokens in turns that
polled [fn: build/coordinator/PROCESS-AUDIT-20261009.md:5 @worktree]; a seat
over a few percent on either is redesigned, not encouraged. For the ACL2
loop, the single batch run per coherent set of edits:

    timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < batch.lsp > out.txt 2>&1

read once, rather than one form per run (lesson 11 for what a batch must not
do to its own measurements).
