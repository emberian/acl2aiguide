# examples/assured: certified shapes for part 3

Small books, one or two techniques each, for `assured/` ("a framework for
assured TigerStyle with ACL2"). None depends on fn2: each is written from
fn2's working forms (cited by path and sha in its header) at the size of
one page. Every book certifies with `examples/certify.sh assured/<book>.lisp`
(ACL2 8.7, SBCL 2.6.8, laptop) in under two seconds, and includes only
community books the laptop has certified (`sources.md`, "Toolchain").

| book | what it shows | chapter |
|---|---|---|
| `columns.lisp` | `defcols`, a one-page `defcolumns`: widths in setter guards, rows bound in the type, init as the only resizer, enum count constants, a registry row, per-array facts by one generic template and disabled after use | 1, 4 |
| `budget.lisp` | a budget as measure, guard and theorem: the run loop's measure is the step budget; the work step's guard is the budget it spends; one run copies at most the cap | 1 |
| `ownership.lisp` | ownership states as an enum column with a generation: stale handles refused first, no reuse while borrowed, generations only grow | 1, 7 |
| `named-stop.lisp` | assert, never absorb: the absorbing shape (evaluated leak), the proved shape (refusal branch deleted, invariant proved), the stopped shape (named reason, first wins) | 1 |
| `machine.lisp` | `defmach`: continuations that name existing guard-verified functions, checked against the world at admission; dispatch refuses an unknown phase by name | 1 |
| `sim.lisp` | a seeded deterministic simulator: faults chosen after the flight from applicable classes, landings counted at effect, a witness checker against a verdict checker, a mutant server, draws against landings | 2 |
| `square-paste.lisp` | a G1 square with a stuttering label interpretation, pasted along words once in an `encapsulate`, instantiated for a fused executor against a reference; a mutant whose step obligation is false | 3 |
| `diamond.lisp` | a G2 diamond by footprints, proved once; the accept/close false diamond: different machines, different admissions | 3 |
| `nth-cost.lisp` | the generic per-array NTH rule family against field-specific rules, with the measured cost table (time grows much faster than steps) | 4 |
| `summary-upto.lisp` | the summary certificate as the converter's graph up to a `defequiv`/`defcong` congruence (`gu-graph-upto-fold`), instantiated for a parity counter whose homomorphism is refuted | 5 |
| `registry-emit.lisp` | a table-only export cannot see a behaviour-only generator mutation; a manifest of admitted bodies can | 6 |
| `owed.lisp` | `defthm-owed` and `defthm-claimed` rows in a world table, teeth that name evaluating functions, counts read from the world | 6, 7 |

Every refusal shown by `must-fail` in these books was rerun without the
wrapper and its failure read (the reason is the one the book's comment
states), following the pitfall recorded in `examples/transport/README.md`.
