# 7. The honest costs: what is proved, what is owed, what the method does not buy

A passing check can leave the advertised theorem unproved.
At fn2 revision `127f7b877`, the exported ledger contains 22 obligations,
all owed; its header explicitly says that executable teeth are evidence,
not proofs. That is the starting point for assessing this working instance
of assured TigerStyle. [fn: fn2/docs/OWED.md:6 @127f7b877]

## 7.1 Count the statements without counting them as proofs

The first reporting mistake is to put theorem forms, generated events,
evaluated witnesses and top-level obligations into one total.
The pinned ledger separates owed statements from theorem admission:
`defthm-owed` defines a non-executable statement function and records
`:status :owed`; its expansion contains no `defthm`.
[fn: fn2/books/owed.lisp:11 @127f7b877]

Measured on 2026-10-29, the exported table has **22 rows, 22 owed,
0 proved**. This measures the checked-in export at the pinned revision;
it does not rerun its exporter.
[measured: `git -C ~/dev/fn show 127f7b877:fn2/docs/OWED.md | awk '/^\| `/{rows++; if ($0 ~ /\| :OWED \|/) owed++; if ($0 ~ /\| :PROVED \|/) proved++} END {print rows, owed+0, proved+0}'`, output `22 22 0`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

The hand-written source contains **236 column-zero `defthm`/`defthmd`
forms** in `fn2/books` and `fn2/sim`. This is a deliberately syntactic
inventory: indented forms and macro expansions are outside that count.
[measured: `git -C ~/dev/fn grep -h -E '^\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `236`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

Allowing leading whitespace gives **340 source occurrences**, including
the hand-written templates inside generators. That broader grep still
counts template text, not the events produced by expanding it.
[measured: `git -C ~/dev/fn grep -h -E '^[[:space:]]*\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `340`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

The expanded theorem inventory is larger and is not counted here:
the column generator emits accessor, bound and preservation theorems
repeatedly, recursing over the columns. Neither grep result is a count
of proved top-level guarantees. [fn: fn2/books/columns.lisp:493 @127f7b877]
[fn: fn2/books/columns.lisp:539 @127f7b877]

The 22 owed rows divide as follows; each count is scoped to that export.
[fn: fn2/docs/OWED.md:12 @127f7b877]

| Family | Rows | What remains owed |
|---|---:|---|
| Pool | 5 | Stale-handle refusal, byte-fill, no reuse while borrowed, conservation, generation monotonicity and retirement. [fn: fn2/docs/OWED.md:12 @127f7b877] |
| Operation vocabulary | 4 | Credit conservation, stale or duplicate posting, outbox order, result reservation. [fn: fn2/docs/OWED.md:17 @127f7b877] |
| Core issue refusal | 9 | Receive, send, read, write, fence, accept, close, cancel and entropy preserve the logical core on refusal. [fn: fn2/docs/OWED.md:22 @127f7b877] |
| Composed harvest | 1 | Expose exactly the initialized loan prefix after successful adapter writes and the posted completion. [fn: fn2/docs/OWED.md:31 @127f7b877] |
| Turn bounds | 1 | Simultaneous observation, calendar-visit and action-descriptor bounds. [fn: fn2/docs/OWED.md:32 @127f7b877] |
| Turn refinement | 1 | Correspondence with independent list selection and accounting, sharing machine semantics. [fn: fn2/docs/OWED.md:33 @127f7b877] |
| Scheduler starvation | 1 | A continuously eligible principal receives an opportunity within the calendar length. [fn: fn2/docs/OWED.md:21 @127f7b877] |

The release plan's older sentence, "Twenty-one obligations with evaluated
teeth, none proved", is stale for this pin: its list says eight issue
refusals, while the export contains nine, including entropy.
The source export determines this chapter's count.
[fn: build/coordinator/fn2/RELEASE-PLAN.md:251 @worktree, read 2026-10-29]
[fn: fn2/docs/OWED.md:30 @127f7b877]

## 7.2 A certified ledger can contain an unproved, even false, conjecture

A successful certification does not turn every formula mentioned in a
book into a theorem. The manual describes `defthm` as "Prove and name a
theorem"; `assert-event` instead checks that evaluation "returns a
non-`nil` value, causing an error otherwise". [:doc defthm]
[:doc assert-event]

The small ledger example makes the distinction executable.
`defthm-claimed` emits a `defthm` followed by a proved row.
`defthm-owed` translates its formula, runs the named tooth functions,
and records an owed row. `claim-counts` reads that table from the world.
[example: examples/assured/owed.lisp]

These are the example's forms, with their existing definitions in scope:
[example: examples/assured/owed.lisp]

```lisp
(defthm-claimed sat-inc-bounded
  (implies (natp x) (<= (sat-inc x) (max x *sat-max*))))

(defthm-owed sat-run-monotone (x n)
  (implies (and (natp x) (natp n)) (<= x (sat-run x n)))
  :teeth (sat-run-teeth))

(assert-event (equal (claim-counts (w state)) '(1 1)))
```

The asserted result is **one proved row and one owed row**, in that order.
The teeth check saturation from 250 over ten increments and a wrapping
sibling at 255. They do not establish the owed formula for every natural
starting value. Indeed the owed formula is false: at `x = 256`, `n = 1` its
conclusion reduces to `256 <= 255`, and the book proves that as
`sat-run-monotone-false-at-256`. The row was recorded, its statement
translated, its teeth passed and the book certified; none of that made
it a theorem, and the degenerate corner the teeth did not visit is where
it fails.
[example: examples/assured/owed.lisp]

The ownership example supplies a different kind of evidence:
`slot-free-stale`, `slot-free-refuses-borrowed` and
`slot-free-generation-monotone` are proved for its small pool.
They do not discharge fn2's corresponding pool obligations.
[example: examples/assured/ownership.lisp]
[fn: fn2/docs/OWED.md:12 @127f7b877]

Its demonstration asserts exactly this sequence of answers and final
generation; it does not assert that the production pool has been proved.
[example: examples/assured/ownership.lisp]

```lisp
(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

The earlier process chapter already covers witness construction and failed
proof searches: "A negated `must-fail` is not a counterexample."
The teeth lesson adds the practical search direction: "Hunt the degenerate
corners first: empty sets, zero, values outside the intended type."
[guide: humans/06-process.md:113]
[guide: fn-lessons/23-teeth.md:61]

## 7.3 The refinement name is broader than the present statement

The dangerous reading of `fn2-turn-refinement` is "the server implements
the execution model". Its own description is narrower:
"Owed refinement to independent list selection, observation ordering and
budget accounting; shared bounded machine semantics, no fusion."
[fn: fn2/books/reference.lisp:248 @127f7b877]

The reference selects work independently, but calls the implementation's
harvest and observation handlers, machine runner, clock update and service
operations. A shared handler defect can therefore survive the comparison.
The review's S2 finding identifies this weakness; the pinned code still
shows the shared calls. [fn: fn2/books/reference.lisp:92 @127f7b877]
[fn: fn2/books/reference.lisp:142 @127f7b877]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]

The owed conclusion equates status and counters, preserves the core
recognizers and representation relation, and bounds actions and reported
work. Its work inequality uses `24` and `4129`; S2 calls these
self-declared constants. This is not a measured CPU bound.
[fn: fn2/books/reference.lisp:254 @127f7b877]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]

EXECUTION-MODEL section 4 asks for more: boundary compatibility,
initialization, semantic invariant preservation, output and effect
correspondence, resumable progress, fusion and crash composition,
including every submitted-action prefix and death cut.
The present owed turn statement does not discharge that contract.
[fn: build/coordinator/fn2/EXECUTION-MODEL.md:27 @worktree, read 2026-10-29]

Composition does not erase this difference. In the pinned Lean source,
`q1_licensed` requires a square for every catalogue case and concludes a
square for words over those cases. Its premises remain parameters;
the theorem supplies no ACL2 instance proofs.
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:56 @dddc32d34]

The certified square example shows a smaller, completed application:
`fused-refines-reference` uses the generic `sq-paste-obs` after the
instance's step and observation lemmas. Its tooth asserts totals of
12 for the correct fused step, 5 for the mutant and 12 for the reference;
`fused-step-bad-breaks-square` proves the mutant violates the step relation.
[example: examples/assured/square-paste.lisp]

The manual states the remaining obligation directly: "before such a lemma
instance can be used, the system will generate proof obligations" from
substituting functions into supporting constraints. Reuse saves the
generic argument; the concrete instance still has work to do.
[:doc lemma-instance]

## 7.4 The estimates are substantial, scoped, and not elapsed work

A plan can make expensive work look finished by naming its generators.
The DSL proposal explicitly says it "proves nothing by itself":
it states obligations, enumerates cases and exposes gaps.
Its budget must be read as proposed engineering work.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:32 @worktree, read 2026-10-29]

The pessimistic estimate is **13 engineer-days for the first three
quests**, DM0a, DM1 and DM0b: identities and manifest, obligation storage,
then callbacks, staging and seals. Those quests are part of the larger
plan, not an additional thirteen days.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:34 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/DSL-METATHEORY.md:544 @worktree, read 2026-10-29]

The pessimistic estimate is **100 engineer-days for the mandatory
metatheory packages**, excluding R5e, R6a, R6b and R7 themselves,
and excluding the generator experiment's replay and campaign work.
DM3 supplies part of that experiment; these budgets cannot be added
without reconciling their overlapping deliverables.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:559 @worktree, read 2026-10-29]

The pessimistic estimate is **12 engineer-days plus several machine-days
for the replay-based generator experiment**: explicit choices and replay,
transition correspondence and comparison, mutation controls, then bounded
enumeration and measurement. It excludes generic recursive checkpoints,
partial-order reduction and a universal declaration form.
[fn: build/coordinator/fn2/COHERENCE.md:862 @worktree, read 2026-10-29]

The Lean decisions price four further scopes pessimistically.
These are estimates, not a timesheet, and the bridge explicitly overlaps
the DSL work. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:211 @worktree, read 2026-10-29]

| Pessimistic estimate | Scope |
|---:|---|
| 2 engineer-days | Advisory reporting: model freshness, theorem status, instance bindings and named failures. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:215 @worktree, read 2026-10-29] |
| 8 engineer-days | The qualified Lean foundation, including the proposed mixed-pasting and toy-completeness extensions. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:216 @worktree, read 2026-10-29] |
| 7 engineer-days | Exact translated-statement binding and generated-artifact provenance, inside or beside DM0a/DM1. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:217 @worktree, read 2026-10-29] |
| 5 engineer-days | Emitter extension for B's tables, identity and order checks, deterministic serialization. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:218 @worktree, read 2026-10-29] |

The proposed experiment has an explicit losing outcome: no useful
improvement over sampling with the same instrumentation and monitors.
Its comparison includes replay, checking and garbage collection.
The payoff on fn2's workload remains unmeasured in this design record.
[fn: build/coordinator/fn2/COHERENCE.md:855 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:860 @worktree, read 2026-10-29]

## 7.5 The measured costs do not all favor the framework

A generator can make repeated proof work cheap to write and expensive
to run. W1's recorded repair reduced the **sum of certification times
from 1,876 s to 284 s** for the measured layer-A closure, with two jobs
on the laptop. The precise sums are 1,876.11 s and 284.41 s;
they are not wall-clock build durations.
[fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:9 @worktree, read 2026-10-29]

Commit `1fa1fe24b` records the repair; its report compares 60 original
books with 72 final books after assembly splitting.
The main defect was generic numeric-array `nth` inference matching
unrelated fields throughout generated preservation proofs.
The fix uses those facts to derive the accessor API, then disables the
broad rules while retaining field-specific facts.
[fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:11 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read 2026-10-29]

This was a generator lesson learned after its cost had spread through
the closure. The report measures certification cost and records unchanged
contracts; it does not establish the total engineer-time spent discovering,
repairing and reviewing the defect.
[fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:15 @worktree, read 2026-10-29]

The small `nth-cost` book records the same comparison on ACL2 8.7,
SBCL 2.6.8, laptop, 2026-10-29. These are its published measurements,
not fresh timings from this chapter.
[example: examples/assured/nth-cost.lisp]

| Fields | Specific rules only | Specific and generic rules |
|---:|---:|---:|
| 12 | 0.00 s; 1,164 steps | 0.04 s; 1,659 steps |
| 24 | 0.01 s; 2,292 steps | 0.50 s; 3,879 steps |
| 36 | 0.02 s; 3,420 steps | 2.07 s; 6,675 steps |

Both versions prove the same bound; elapsed proof cost grows much more
than the reported step count. A step budget alone would miss this cost
family. [example: examples/assured/nth-cost.lisp]

Experiment B's pessimistic result is **72 hand-written code lines to
obtain 71 generated lines of statements and definitions**, for the toy
cursor representation change. Its full generated expansion has 1,242
printed lines, including proof instructions; that larger number is not
hand-written work saved.
[fn: build/coordinator/fn2/TRANSPORT.md:548 @worktree, read 2026-10-29]

The experiment carries user theorems through `propagate-iso`, after
hand-written base functions, maps and correspondence proofs.
At this scale it demonstrates transport, not a reduction in source work;
scaling to fn2's generated accessor families remains unmeasured.
[example: examples/transport/cursor-iso.lisp]
[fn: build/coordinator/fn2/TRANSPORT.md:555 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29]

## 7.6 The apparatus is part of the bill

The framework can repeat the problem it was meant to remove.
H2 reports that the reviewed harness branch adds **about 210,000 lines
against a core of about 10,000**, including a large hand-maintained
judgment dictionary and committed generated inventories.
This is the review's approximate count for harness revision `5b641fc0a`,
not a fresh measurement of `127f7b877`.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:8 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:132 @worktree, read 2026-10-29]

The earlier apparatus lesson says, "Count the apparatus as part of
the system's size", and asks each checker to name its contract and the
defect class it has found. H2's concrete remedy is schema-checked data
for judgments and build outputs for generated inventories.
[guide: fn-lessons/06-the-apparatus.md:64]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:132 @worktree, read 2026-10-29]

The newer plans therefore need their own cost accounting: manifests,
bridges, serializers and reports are maintained software.
TRANSPORT's warning locates the expense in retention, dependency identity,
activation, recovery, compatibility and resource accounting, rather than
in the number of files alone.
[fn: build/coordinator/fn2/TRANSPORT.md:442 @worktree, read 2026-10-29]

## 7.7 What remains outside the result

A composition theorem can be correct while the claim made from it is
wrong. The following boundaries are stated by the working design and
experiments; none disappears because a registry row typechecks.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:179 @worktree, read 2026-10-29]

- **The actual environment.** X rows describe environmental containment
  assumptions. They are not squares discharged by composition.
  Native experiments provide evidence that real devices and adapters
  meet a model, not a proof that every native behavior is contained in it.
  [fn: build/coordinator/fn2/COHERENCE.md:42 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29]
- **Liveness.** Equal observations on finite prefixes do not establish
  eventual replies or dependency completion. The owed scheduler row
  promises an opportunity bound, explicitly not machine completion.
  [fn: build/coordinator/fn2/COHERENCE.md:130 @worktree, read 2026-10-29]
  [fn: fn2/docs/OWED.md:21 @127f7b877]
- **Completeness of the generators.** Sound composition covers diagrams
  constructed from the supplied generators. Showing that every intended
  interchangeable route is connected by such a diagram is separate;
  the Lean account says frame completeness is not established.
  [fn: build/coordinator/fn2/LEAN-METATHEORY.md:132 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/LEAN-METATHEORY.md:183 @worktree, read 2026-10-29]
- **Unbounded correctness from bounded checks.** A general implication
  cannot promote finite check evidence into its universal premise.
  Checked ACL2 rows remain owed, with conclusions limited to covered runs
  whose states and contracts actually compose.
  [fn: build/coordinator/fn2/LEAN-METATHEORY.md:146 @worktree, read 2026-10-29]
- **Independent semantics from shared handlers.** Agreement can preserve
  the same defect on both sides. OWN, client oracles and semantic contracts
  retain independent work.
  [fn: build/coordinator/fn2/COHERENCE.md:815 @worktree, read 2026-10-29]
- **Automatic speedup or parallel execution.** Replay and comparison may
  consume the savings; scheduler and allocator effects constrain independence.
  Neither faster checking nor a faster runtime follows from declarations.
  [fn: build/coordinator/fn2/COHERENCE.md:813 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/COHERENCE.md:817 @worktree, read 2026-10-29]
- **Storage history or the served representation from a toy transport.**
  Experiment A does not establish historical availability in storage;
  B does not connect its logical rows to served columns.
  [fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29]

The summary example makes the observation boundary concrete.
`par-summary-adequate` proves parity agreement after every suffix;
its assertion checks parity `1` on both sides and a summary step count
of `5`. It does not assert equality of the representations.
[example: examples/assured/summary-upto.lisp]

Performance remains measured and published, never a performance gate
under this release policy. That policy does not remove resource
requirements: the release plan separately identifies W13's resource
guardrail as a gate.
[fn: build/coordinator/fn2/COHERENCE.md:814 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/RELEASE-PLAN.md:279 @worktree, read 2026-10-29]

The reporting rule is therefore concrete: quote the pessimistic estimate
with its scope in the same sentence; report measurements with their
revision, toolchain and domain; keep proof status separate from check
coverage. A checked row stays owed. A proof budget that expires records
an unproved obligation and diagnostics, not a counterexample.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:559 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/DSL-METATHEORY.md:594 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/RELEASE-PLAN.md:213 @worktree, read 2026-10-29]
