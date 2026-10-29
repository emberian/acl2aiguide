# Part 3: assured TigerStyle with ACL2

A framework for writing systems software in the TigerStyle discipline
(bounded everything, static allocation, assertions that stop rather than
absorb, deterministic simulation as the gate) where ACL2 carries the
rules: declarations emit the guards, bounds and theorems; a simulator in
the logic, with checkers that compare witnesses, is the everyday gate;
every correctness claim is a commuting square whose local cases a checker
or a proof consumes; representation changes transport their clients'
theorems; and a Lean metatheory states the frame theorems that ACL2's
instances plug into.

It is written from a working instance, not from intent: fn2, the rebuild
of the ACL2-verified NNTP server fn (`fn-lessons/` tells fn's story). Its
layer A (the byte pool, the event vocabulary, the scheduler and executor,
three probe machines, the simulator and its checkers) is on the fn
repository's branch `fn2/main` at `127f7b877`; its Lean metatheory is on
`fn2/lean-meta` at `dddc32d34`; its design record is in `fn2/docs/design/`
and in fn's coordinator notes, cited `@worktree` with the date read. Where
fn2 got a rule wrong, the chapter says so with the path and line, and fn2's
own review (cited as `REVIEW-SINS-20261028.md`) is the source for most of
those findings.

Part 1 (`humans/05-high-performance.md` section 5.7) translates
TigerStyle's rules into ACL2 one at a time. This part is about keeping them
true across a code base that many authors, most of them agents, write.

## How to read it

- **Humans** read `assured/humans/` in order.
- **Agents** load `assured/ai/NN-*.md` for the task at hand; each is the
  terse twin of the humans chapter with the same number.
- Every technique has a small certified book in `examples/assured/`
  (`examples/assured/README.md` maps books to chapters); none depends on
  fn2.

## Chapters

- `01-rules-as-declarations`: TigerStyle's rules as declarations: bounds in
  guards and types, budgets as guards and measures, no allocation after
  init, ownership states with generations, assert never absorb (named
  stops), with `defcolumns` and `defmachine` as the worked forms.
- `02-simulation-and-checkers`: deterministic simulation with independent
  checkers as the gate: seeded and replayable, fault landings counted (not
  draws), checkers that compare witnesses not verdicts, mutation controls.
- `03-commuting-squares`: every correctness claim as a commuting square:
  the inventory, the generating set (G0, G1, G1q, G2), the three pastings
  and their premises, independence by footprints, the false diamond, what
  squares do not buy, and how ACL2 states them.
- `04-certify-cost`: the one-minute rule and the certify-cost discipline:
  the per-array rule family that dominated fn2's certify time, generic
  templates, pinned theories, the cost contract, splits, and why the step
  counter missed it.
- `05-transport`: transport across representations: functional
  instantiation, `propagate-iso` and its measured cost, the summary
  certificate in its relational and up-to-congruence forms.
- `06-metatheory-split`: Lean for frame theorems, ACL2 for instances, the
  DSL emitting its Lean presentation, the bridge assumption, the measured
  limit (table reads miss behaviour-only changes), and "a reading is not a
  build".
- `07-honest-costs`: proved against owed, the 100-engineer-day plan, the
  costs already paid, and what the method does not buy.
