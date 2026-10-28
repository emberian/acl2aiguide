# Lane C: high-performance software in ACL2; the process

Read `~/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `humans/05-high-performance.md`
- `humans/06-process.md`
- `examples/performance/*.lisp`, `examples/process/*.lisp`

## Chapter 5: high-performance software in ACL2

The executable/logical split: `mbe` and guards as the mechanism; what runs
when (guard-verified bodies run raw Lisp; `*1*` bodies evaluate every
callee's guard and `mbe` runs `:logic`; `:program` mode) [fn
docs/proof-style.md section 11 "The executed path is what counts", `mbe`,
`guard`, `evaluation`]. Static allocation and fixed-size stobjs: `defstobj`
array fields with `:initially`, `:resizable nil` vs `t` and the cost of
`resize-*`, `(unsigned-byte 8)` and `(unsigned-byte 61)`/fixnum fields
(fn `books/msgid-linear-exec.lisp`: "every word is a fixnum on SBCL x86-64
so the accessor returns it unboxed and the scan allocates nothing";
measured 16 bytes consed per lookup vs 6,364), `:inline`, `the` and
`declare` `type`/`optimize`; `with-local-stobj` for scratch space. No
consing on hot paths: how to find consing (`(time$ ...)` and its `:mintime`/
`:msg`, SBCL's `sb-ext:get-bytes-consed` as fn used it, `profile`/
`memsum`, `(comp t)`, the `hons-summary`), the fn hot-path checker's idea
(`tools/hot_path_check.py`: a served entry walks only what its request
touches; what it cannot see) [fn docs/proof-style.md section 11,
`time$`, `profile`, `comp`, `lisp-performance` topics if present (look them
up), `hons-and-memoization`]. The representation lesson: octet lists cost
sixteen bytes per octet; fn asked six times for concrete representations
and the list paths were never deleted (`REPRESENTATION-HISTORY-20261028.md`;
cite the table: `fnn-octet-list` calls grew 130 to 263 after D27). Batching
and group commit as modelled state (the log batch, one barrier per batch of
commits: fn `books/store-log.lisp` header on origin/dev; `specs/storage.md`
STO-028/034). One executor loop: actions, completions, slots, pool,
leases, the borrowed view (fn `books/runtime-contract.lisp` header, the
`RUNTIME-MODEL` sections it cites). TigerStyle translated to ACL2: read
TigerBeetle's TIGER_STYLE (fetch it with `curl -sL
https://raw.githubusercontent.com/tigerbeetle/tigerbeetle/main/docs/TIGER_STYLE.md`
into your scratchpad; if the fetch fails, say so and skip the quotes rather
than paraphrase from memory) and map each rule: assertions become guards
and `assert-event`/`mbt`; "bounded everything" becomes explicit limits as
`defconst` and `:guard` conjuncts and bounded loops with measures;
"no allocation after init" becomes fixed stobjs and `with-local-stobj`;
deterministic simulation becomes the step function over an event list with
a seeded generator in a test book; "the system is the loop" becomes one
executor. Code generation: Kestrel's ATC (ACL2 to C: what subset, the
shallow embedding, how a function with `(unsigned-byte 32)` guards becomes
C, the generated theorems; `kestrel/c/atc/doc.lisp`, `tutorial.lisp`, and
`tests/*.lisp` with their `.c`) and APT (program transformation:
`isodata`, `expdata`, `parteval`, `finite-difference`, `casesplit`,
`lift-iso`, each with its `-doc.lisp` and `-tests.lisp`) as the route to a
tiny shipped core; what fn's extractor was instead (ANATOMY "Images";
EMBER.md 35f3668a#1588 "do we really need to be using ACL2's runtime";
bare SBCL). What a metaprogramming layer buys and costs: fn's generators
(`fn-defrecord`, `def-loop`, `def-representation`, `def-carried`,
`definterface`, `defteeth`) measured against what they replaced (lines,
inductions, hand obligation blocks: docs/proof-style.md table at the top,
def-loop.lisp header, ANATOMY sin 1 and 3), the cost (a static reader
cannot see through a macro: fn had to mirror `fn-defrecord` in Python;
`make-event` is invisible to static tools), and a sketch of the three DSLs
the brief names (a record/column DSL, a machine DSL, a command-grammar DSL)
as the shape of fn2, grounded in what `def-representation` and the
`protocol-table` (`books/protocol-table.lisp`, the `fn-proto-text` macro)
already did.

## Chapter 6: process

Statement-first: a keystone enters as a statement with its satisfiable
premise, its teeth and its subject before proof work; "a wrong statement
proved fast is the expensive failure" [minidregg CLAUDE.md law, quote it as
`~/dev/minidregg/CLAUDE.md`; fn docs/proofs.md "Shape of the
claims"; OWED.md top-level-theorems section]. The premise/teeth/satisfiable
discipline, with the fn false-OB-2 story if `cv search 'OB-2'` finds it.
What to prove early vs late (semantics-first: build the implementation,
test it classically, then prove what you want assurance from: ember's
words in EMBER.md adb603dc#2736 and be1e9dcf#4275 "sometimes we shouldn't
do those at the same time"; the counter-risk: a representation designed
for the proof, ANATOMY "competing representations were originally designed
to make the refinement proofs easier"). How not to drown in checkers and
ledgers: fn's third sin (ANATOMY: 301K lines of registers, 45K of
checkers, 130K of tests, 55K of planning prose; "the apparatus outgrew the
organism"), the two-week audit's collapse targets
(AUDIT-TWO-WEEKS section c), what to keep (one generated ledger, teeth
inside ACL2 as `must-fail`/`assert-event`, the certify gate) and what to
delete. How to size proofs: the ten-second rule and the steps ratchet (fn
docs/proofs.md "proof_cost"), split a book at 800 lines at its seam
(docs/proof-style.md section 6), the include-closure cost and "prefer a new
book low in the table", one world and no twins (ANATOMY, CUT-M2 "one
world"). When to skip-proofs honestly: `:doc skip-proofs`'s own words,
fn's rule "skip-proofs is forbidden by the certifier; a broken theorem is
deleted with an OWED row" (lanedump A4), a ledger row as the honest form.
How to run ACL2 as a REPL from an agent: one session that stays alive
(`proof_repl.py`'s design: `start NAME BOOK --upto EVENT`, `send`,
`send-range`, `probe` with a checkpoint undo, `with-prover-time-limit` on
every form, idle timeout; docs/proofs.md "proof work gets a live session"),
certify a changed book yourself before reporting, the host and cache
pitfalls (`ACL2_BOOK_HASH_ALISTP=NIL`, certificate validity is the closure,
`.fasl` travels with the pair, a `.cert` beside a book proves nothing after
a merge: docs/proofs.md "Certificates"), the continuation's measured
rules (`cut-m2a-lb-continuation.md` "How to run": the REPL refuses to
redefine a changed function; stop and restart after an edit; background
everything over 100 s; never `sleep` in the foreground). The process
lessons from PROCESS-AUDIT-20261009.md (foreground waits 32% of seat time;
zero summary-based restarts) stated as rules.

## Examples to write and certify

At least: an `mbe`/guard pair where the `:exec` is a fixnum loop over a
stobj array with `(the (unsigned-byte 61) ...)` declarations and a theorem
equating it to the list recursion; a fixed-size stobj with
`:resizable nil` and bounded insert returning a typed refusal when full; a
`time$`-instrumented comparison in a test book (list vs stobj) whose
numbers you report as `[measured: ...]`, with the `.cert.out` as the
record; a seeded deterministic-simulation test book (a step function run
over a generated event list, `assert-event` on the invariant at every step)
with a bounded loop and a measure; a `defconst`-bounded limits table used
as guards; a tiny "statement-first" book: the `defthm` statement under
`must-fail` of its mutant and `assert-event` of its witness before the
proof. ATC/APT are shown from their own tests (not certified here). Each
example certifies with `examples/certify.sh`.

## Report

READY with the two chapters, the examples' Built lines, the sources block,
the README lines; or BLOCKED.
