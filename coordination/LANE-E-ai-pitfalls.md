# Lane E: part 2 for AIs, the pitfalls-first checklist and the form shapes

Read `/Users/ember/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `ai/00-pitfalls-first.md` (the ten-plus ways an agent wastes a day in
  ACL2, each with its fix; written to be loaded into an agent's context)
- `ai/01-form-shapes.md` (the forms that work: copy them, do not guess)
- `ai/02-reading-the-manual.md` (XDOC from a shell; the REPL as a tool; how
  to batch verification instead of one-statement loops)
- `examples/shapes/*.lisp` (every shape in 01 certifies)

## Method: mine the transcripts, then verify against the manual

The pitfalls are in the transcripts. `cv search '<term>'` (default 20 hits
shown; `--limit 200`; `--json` for scripting) finds the sessions;
`cv show <id> --around N` reads the episode. Terms that find real wounds
(each has hundreds of hits): `Step-limit`, `free variable`,
`skip-proofs`, `defabsstobj-missing-events`, `with-local-stobj`,
`There is no certificate on file`, `HARD ACL2 ERROR`, `Guard violation`,
`single-threaded`, `stobj-let`, `must-fail`, `minimal-theory`,
`functional-instance`, `accumulated-persistence`, `key checkpoint`,
`ubt`, `portcullis`, `The proof of the guard`, `non-recursive`,
`prover-step-limit`, `ACL2 Error in ( DEFTHM`, `ACL2 Error in ( DEFUN`,
`ACL2 Error in ( VERIFY-GUARDS`, `ACL2 Error in ( INCLUDE-BOOK`,
`ACL2 Error in ( DEFABSSTOBJ`, `ACL2 Error in ( DEFSTOBJ`, `illegal`,
`in-package`, `defpkg`, `mv-let`, `:program`, `redefin`, `ld-skip-proofsp`,
`rewrite loop`, `backchain`, `generalizing`, `destructor`, `fertiliz`.
For each pitfall you keep: find at least two independent episodes (two
sessions), read how it looked in ACL2's output, read how it was fixed, and
then read the manual topic that explains the mechanism and cite it. A
pitfall with one episode is an anecdote; a pitfall with no manual
explanation is a rumour. The fn lane continuation
`/Users/ember/dev/fn/build/coordinator/lanedumps/cut-m2a-lb-continuation.md`
("How to run": with-local-stobj's shape; the REPL refusing to redefine)
and fn `docs/proof-style.md` sections 9.1 to 9.3 are three pitfalls
already written up with measurements; use them.

Then rank: by the time wasted (the episode's wall-clock from the
transcript timestamps, `cv show` prints them) times how often it recurs.
The chapter opens with the ranked list, one line each, then one section
per pitfall: the symptom as ACL2 prints it (quoted), the mechanism
(`[:doc]`), the fix (a form), and the citation(s) `[cv: ID#N]`.

Candidates the coordinator expects to see (verify each; drop what the
transcripts do not support): the step-limited probe that measures nothing;
`:use` adds a hypothesis and does not rewrite; a `Goal` `:in-theory` lost
under a subgoal hint; a free variable in a rewrite rule's hypothesis that
never binds; `with-local-stobj` returning the stobj; the `mv` arity and
stobjs-out mismatch; `in-package`/`defpkg` and the portcullis when
certifying; "There is no certificate on file" cascading through a closure;
a `local` lemma used by a dependent (the book certifies, the includer
fails); editing a book and certifying the wrong thing (the REPL world vs the
certificate); the loop that `accumulated-persistence` names; `skip-proofs`
in a certified book; a `defthm` whose statement is vacuous (hypotheses
unsatisfiable; teeth); the whole-state recognizer opened in a transition
proof (1,082 subgoals); the book-wide `enable`; `minimal-theory` as a
reflex; the general negated `must-fail`; guard verification needing a
`:rule-classes nil` equality by `:use`; `len`-backchaining; a `:linear`
with a `:rewrite` twin; an hour-long `cert.pl` of a closure when one form
in a REPL answers; polling and foreground waits (PROCESS-AUDIT); restarting
from a summary instead of resuming the agent.

## 01-form-shapes.md

For each shape: the form whole, then one line on when, then the example
file that certifies it. Shapes (at least): `defun` with `:guard`,
`:measure`, `:verify-guards nil` and a later `verify-guards`; `defthm` with
each rule class; `:rule-classes nil` used by `:use`/`:instance`;
`defthm` with `:hints` (`:use`, `:cases`, `:expand`, `:induct`,
`:in-theory (e/d ...)`); `local` + `encapsulate` with a constrained
function and its `:functional-instance`; `defstobj` with array and
hash-table fields and the updater/accessor theorems; `with-local-stobj`
with `mv`; `stobj-let`; `defabsstobj` with every obligation; `mbe` loop
twin; `memoize`; `make-event`/`assert-event`/`must-fail` teeth;
`include-book` with `:dir :system` and a `local` include; the `.acl2`
portcullis with `defpkg`; `cert.pl` invocation; a driver `.lsp` for the
REPL with `(set-gag-mode :goals)`, `(with-prover-time-limit ...)`,
`:brr`, `:pe`, `:pl`. Every shape lives in `examples/shapes/` and
certifies.

## 02-reading-the-manual.md

How to read XDOC from a shell (the `grep`/`sed` recipe in COMMON.md and
the `:doc` render; `xdoc::save`? only if you verify it works here);
`:doc`, `:args`, `:pe`, `:pl`, `:pr`, `:pbt`, `:pc`; the `acl2-doc` Emacs
browser named only; how to run ACL2 as a REPL from an agent: one session
with forms batched in a driver file under `timeout`, read the output once,
`(set-gag-mode :goals)` and `(set-inhibit-output-lst ...)` to shrink it;
the batching rule from ember's words (EMBER.md 2026-10-27: "iterating
across the whole system and using mental simulations and reasoning in our
mind to metarationally develop without wasteful rerun loops"): simulate
the proof in your head first, write the whole book, certify once, read
every checkpoint, fix all of them, certify once; never one form per run;
`ld` with `:ld-pre-eval-print t` for a driver; `cert.pl` for closures;
`ACL2_BOOK_HASH_ALISTP=NIL` and what a certificate covers.

## Report

READY with the three chapters, the examples' Built lines, the sources block
(every `[cv:]` and `[:doc]`), the README lines; or BLOCKED.
