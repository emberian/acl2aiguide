# 7. Account for evidence, remaining work and cost

A passing check can leave the advertised theorem unproved. At fn2 revision
`127f7b877`, the exported ledger contains 22 obligations, all owed; its
header explicitly says that executable teeth are evidence, not proofs. That
is the starting point for assessing this working instance of assured
TigerStyle. [^s1]

## 7.1 Report proof status separately from statement counts

The first reporting mistake is to put theorem forms, generated events,
evaluated witnesses and top-level obligations into one total. The pinned
ledger separates owed statements from theorem admission: `defthm-owed`
defines a non-executable statement function and records `:status :owed`; its
expansion contains no `defthm`. [^s2]

Measured on 2026-10-29, the exported table has **22 rows, 22 owed, 0
proved**. This measures the checked-in export at the pinned revision; it
does not rerun its exporter. [^s3]

The hand-written source contains **236 column-zero `defthm`/`defthmd`
forms** in `fn2/books` and `fn2/sim`. This is a deliberately syntactic
inventory: indented forms and macro expansions are outside that count. [^s4]

Allowing leading whitespace gives **340 source occurrences**, including the
hand-written templates inside generators. That broader grep still counts
template text, not the events produced by expanding it. [^s5]

The expanded theorem inventory is larger and is not counted here: the column
generator emits accessor, bound and preservation theorems repeatedly,
recursing over the columns. Neither grep result is a count of proved
top-level guarantees. [^s6] [^s7]

The 22 owed rows divide as follows; each count is scoped to that export.
[^s8]

| Family | Rows | What remains owed |
|---|---:|---|
| Pool | 5 | Stale-handle refusal, byte-fill, no reuse while borrowed, conservation, generation monotonicity and retirement. [^s8] |
| Operation vocabulary | 4 | Credit conservation, stale or duplicate posting, outbox order, result reservation. [^s9] |
| Core issue refusal | 9 | Receive, send, read, write, fence, accept, close, cancel and entropy preserve the logical core on refusal. [^s10] |
| Composed harvest | 1 | Expose exactly the initialized loan prefix after successful adapter writes and the posted completion. [^s11] |
| Turn bounds | 1 | Simultaneous observation, calendar-visit and action-descriptor bounds. [^s12] |
| Turn refinement | 1 | Correspondence with independent list selection and accounting, sharing machine semantics. [^s13] |
| Scheduler starvation | 1 | A continuously eligible principal receives an opportunity within the calendar length. [^s14] |

The release plan's older sentence, "Twenty-one obligations with evaluated
teeth, none proved", is stale for this pin: its list says eight issue
refusals, while the export contains nine, including entropy. The source
export determines this chapter's count. [^s15] [^s16]

## 7.2 A certified ledger can contain an unproved, even false, conjecture

A successful certification does not turn every formula mentioned in a book
into a theorem. The manual describes `defthm` as "Prove and name a theorem";
`assert-event` instead checks that evaluation "returns a non-`nil` value,
causing an error otherwise". [^s17] [^s18]

The small ledger example makes the distinction executable. `defthm-claimed`
emits a `defthm` followed by a proved row. `defthm-owed` translates its
formula, runs the named tooth functions, and records an owed row.
`claim-counts` reads that table from the world. [^s19]

These are the example's forms, with their existing definitions in scope:
[^s19]

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
`sat-run-monotone-false-at-256`. The table entry, translated statement,
passing controls and successful certification all coexist with this
counterexample. The controls did not test that starting value. [^s19]

The ownership example supplies a different kind of evidence:
`slot-free-stale`, `slot-free-refuses-borrowed` and
`slot-free-generation-monotone` are proved for its small pool. They do not
discharge fn2's corresponding pool obligations. [^s20] [^s8]

Its demonstration asserts exactly this sequence of answers and final
generation; it does not assert that the production pool has been proved.
[^s20]

```lisp
(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

The earlier process chapter already covers witness construction and failed
proof searches: "A negated `must-fail` is not a counterexample." The teeth
lesson adds the practical search direction: "Hunt the degenerate corners
first: empty sets, zero, values outside the intended type." [^s21] [^s22]

## 7.3 The refinement name is broader than the present statement

The dangerous reading of `fn2-turn-refinement` is "the server implements the
execution model". Its own description is narrower: "Owed refinement to
independent list selection, observation ordering and budget accounting;
shared bounded machine semantics, no fusion." [^s23]

The reference selects work independently, but calls the implementation's
harvest and observation handlers, machine runner, clock update and service
operations. A shared handler defect can therefore survive the comparison.
The review's S2 finding identifies this weakness; the pinned code still
shows the shared calls. [^s24] [^s25] [^s26]

The owed conclusion equates status and counters, preserves the core
recognizers and representation relation, and bounds actions and reported
work. Its work inequality uses `24` and `4129`; S2 calls these self-declared
constants. This is not a measured CPU bound. [^s27] [^s26]

EXECUTION-MODEL section 4 asks for more: boundary compatibility,
initialization, semantic invariant preservation, output and effect
correspondence, resumable progress, fusion and crash composition, including
every submitted-action prefix and death cut. The present owed turn statement
does not discharge that contract. [^s28]

Composition does not erase this difference. In the pinned Lean source,
`q1_licensed` requires a square for every catalogue case and concludes a
square for words over those cases. Its premises remain parameters; the
theorem supplies no ACL2 instance proofs. [^s29]

The certified square example shows a smaller, completed application:
`fused-refines-reference` uses the generic `sq-paste-obs` after the
instance's step and observation lemmas. Its tooth asserts totals of 12 for
the correct fused step, 5 for the mutant and 12 for the reference;
`fused-step-bad-breaks-square` proves the mutant violates the step relation.
[^s30]

The manual states the remaining obligation directly: "before such a lemma
instance can be used, the system will generate proof obligations" from
substituting functions into supporting constraints. Reuse saves the generic
argument; the concrete instance still has work to do. [^s31]

## 7.4 Keep planning estimates separate from measured work

A plan can make expensive work look finished by naming its generators. The
DSL proposal explicitly says it "proves nothing by itself": it states
obligations, enumerates cases and exposes gaps. Its budget must be read as
proposed engineering work. [^s32]

The pessimistic estimate is **13 engineer-days for the first three quests**,
DM0a, DM1 and DM0b: identities and manifest, obligation storage, then
callbacks, staging and seals. Those quests are part of the larger plan, not
an additional thirteen days. [^s33] [^s34]

The pessimistic estimate is **100 engineer-days for the mandatory metatheory
packages**, excluding R5e, R6a, R6b and R7 themselves, and excluding the
generator experiment's replay and campaign work. DM3 supplies part of that
experiment; these budgets cannot be added without reconciling their
overlapping deliverables. [^s35]

The pessimistic estimate is **12 engineer-days plus several machine-days for
the replay-based generator experiment**: explicit choices and replay,
transition correspondence and comparison, mutation controls, then bounded
enumeration and measurement. It excludes generic recursive checkpoints,
partial-order reduction and a universal declaration form. [^s36]

The Lean decisions price four further scopes pessimistically. These are
estimates, not a timesheet, and the bridge explicitly overlaps the DSL work.
[^s37]

| Pessimistic estimate | Scope |
|---:|---|
| 2 engineer-days | Advisory reporting: model freshness, theorem status, instance bindings and named failures. [^s38] |
| 8 engineer-days | The qualified Lean foundation, including the proposed mixed-pasting and toy-completeness extensions. [^s39] |
| 7 engineer-days | Exact translated-statement binding and generated-artifact provenance, inside or beside DM0a/DM1. [^s40] |
| 5 engineer-days | Emitter extension for B's tables, identity and order checks, deterministic serialization. [^s41] |

The proposal allowed a losing outcome: no useful improvement over sampling
with the same instrumentation and monitors. Its comparison includes replay,
checking and garbage collection. That design record contains an estimate,
not a measured payoff. [^s42] [^s43]

The later E1 pass 2 supplies the search comparison. At the same explicit
search budget, random choices found all six mutations on all three fixed
seeds; iterative deepening and exact-state deduplication each found only
M3/M5/M6. Neither enumerator added a qualified defect missed by random
choices. The result is no demonstrated search advantage on this workload.
[Chapter 2](02-simulation-and-checkers.md#measured-result-e1-pass-2) gives
the budgets, baseline failure, positive local diamonds and scope. [^s44]

E2 pass 3 separately measured the common `defsquare` form: 2,085 physical
source lines, comprising 1,454 new and 631 copied lines. Fourteen lines were
wrapped consumer declarations; 2,071 were support. Its 45 rows split into 40
owed and five proved, with 83 separate evidence records. This is a cost and
status inventory, not net savings: no implemented manual-registration
baseline was available. [Chapter
6](06-metatheory-split.md#a-later-declaration-experiment-e2-pass-3) explains
what the two consumers establish. [^s45] [^s46]

## 7.5 The measured costs do not all favor the framework

A generator can make repeated proof work cheap to write and expensive to
run. W1's recorded repair reduced the **sum of certification times from
1,876 s to 284 s** for the measured layer-A closure, with two jobs on the
laptop. The precise sums are 1,876.11 s and 284.41 s; they are not
wall-clock build durations. [^s47]

Commit `1fa1fe24b` records the repair; its report compares 60 original books
with 72 final books after assembly splitting. The main defect was generic
numeric-array `nth` inference matching unrelated fields throughout generated
preservation proofs. The fix uses those facts to derive the accessor API,
then disables the broad rules while retaining field-specific facts.
[^s48] [^s49]

This was a generator lesson learned after its cost had spread through the
closure. The report measures certification cost and records unchanged
contracts; it does not establish the total engineer-time spent discovering,
repairing and reviewing the defect. [^s50]

The small `nth-cost` book records the same comparison on ACL2 8.7, SBCL
2.6.8, laptop, 2026-10-29. These are its published measurements, not fresh
timings from this chapter. [^s51]

| Fields | Specific rules only | Specific and generic rules |
|---:|---:|---:|
| 12 | 0.00 s; 1,164 steps | 0.04 s; 1,659 steps |
| 24 | 0.01 s; 2,292 steps | 0.50 s; 3,879 steps |
| 36 | 0.02 s; 3,420 steps | 2.07 s; 6,675 steps |

Both versions prove the same bound; elapsed proof cost grows much more than
the reported step count. A step budget alone would miss this cost family.
[^s51]

Experiment B's pessimistic result is **72 hand-written code lines to obtain
71 generated lines of statements and definitions**, for the toy cursor
representation change. Its full generated expansion has 1,242 printed lines,
including proof instructions; that larger number is not hand-written work
saved. [^s52]

The experiment carries user theorems through `propagate-iso`, after
hand-written base functions, maps and correspondence proofs. At this scale
it demonstrates transport, not a reduction in source work; scaling to fn2's
generated accessor families remains unmeasured. [^s53] [^s54] [^s55]

## 7.6 The apparatus is part of the bill

The framework can repeat the problem it was meant to remove. H2 reports that
the reviewed harness branch adds **about 210,000 lines against a core of
about 10,000**, including a large hand-maintained judgment dictionary and
committed generated inventories. This is the review's approximate count for
harness revision `5b641fc0a`, not a fresh measurement of `127f7b877`.
[^s56] [^s57]

The earlier apparatus lesson says, "Count the apparatus as part of the
system's size", and asks each checker to name its contract and the defect
class it has found. H2's concrete remedy is schema-checked data for
judgments and build outputs for generated inventories. [^s58] [^s57]

The newer plans therefore need their own cost accounting: manifests,
bridges, serializers and reports are maintained software. TRANSPORT's
warning locates the expense in retention, dependency identity, activation,
recovery, compatibility and resource accounting, rather than in the number
of files alone. [^s59]

## 7.7 What remains outside the result

A composition theorem can be correct while the claim made from it is wrong.
The following boundaries are stated by the working design and experiments;
none disappears because a registry row typechecks. [^s60]

- **The actual environment.** X rows describe environmental containment
  assumptions. They are not squares discharged by composition.
  Native experiments provide evidence that real devices and adapters
  meet a model, not a proof that every native behavior is contained in it. [^s61] [^s62]
- **Liveness.** Equal observations on finite prefixes do not establish
  eventual replies or dependency completion. The owed scheduler row
  promises an opportunity bound, explicitly not machine completion. [^s63] [^s14]
- **Completeness of the generators.** Sound composition covers diagrams
  constructed from the supplied generators. Showing that every intended
  interchangeable route is connected by such a diagram is separate;
  the Lean account says frame completeness is not established. [^s64] [^s65]
- **Unbounded correctness from bounded checks.** A general implication
  cannot promote finite check evidence into its universal premise.
  Checked ACL2 rows remain owed, with conclusions limited to covered runs
  whose states and contracts actually compose. [^s66]
- **Independent semantics from shared handlers.** Agreement can preserve
  the same defect on both sides. OWN, client oracles and semantic contracts
  retain independent work. [^s67]
- **Automatic speedup or parallel execution.** Replay and comparison may
  consume the savings; scheduler and allocator effects constrain independence.
  Neither faster checking nor a faster runtime follows from declarations. [^s68] [^s69]
- **Storage history or the served representation from a toy transport.**
  Experiment A does not establish historical availability in storage;
  B does not connect its logical rows to served columns. [^s55]

The summary example makes the observation boundary concrete.
`par-summary-adequate` proves parity agreement after every suffix; its
assertion checks parity `1` on both sides and a summary step count of `5`.
It does not assert equality of the representations. [^s70]

Performance remains measured and published, never a performance gate under
this release policy. That policy does not remove resource requirements: the
release plan separately identifies W13's resource guardrail as a gate.
[^s71] [^s72]

The reporting rule is therefore concrete: quote the pessimistic estimate
with its scope in the same sentence; report measurements with their
revision, toolchain and domain; keep proof status separate from check
coverage. A checked row stays owed. A proof budget that expires records an
unproved obligation and diagnostics, not a counterexample. [^s35] [^s73]
[^s74]

[Part 3 contents](../README.md) | [Previous chapter](06-metatheory-split.md)

[^s1]: [fn: fn2/docs/OWED.md:6 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L6).

[^s2]: [fn: fn2/books/owed.lisp:11 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/owed.lisp#L11).

[^s3]: [measured: `git -C ~/dev/fn show 127f7b877:fn2/docs/OWED.md | awk '/^\| `/{rows++; if ($0 ~ /\| :OWED \|/) owed++; if ($0 ~ /\| :PROVED \|/) proved++} END {print rows, owed+0, proved+0}'`, output `22 22 0`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

[^s4]: [measured: `git -C ~/dev/fn grep -h -E '^\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `236`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

[^s5]: [measured: `git -C ~/dev/fn grep -h -E '^[[:space:]]*\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `340`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]

[^s6]: [fn: fn2/books/columns.lisp:493 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L493).

[^s7]: [fn: fn2/books/columns.lisp:539 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L539).

[^s8]: [fn: fn2/docs/OWED.md:12 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L12).

[^s9]: [fn: fn2/docs/OWED.md:17 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L17).

[^s10]: [fn: fn2/docs/OWED.md:22 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L22).

[^s11]: [fn: fn2/docs/OWED.md:31 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L31).

[^s12]: [fn: fn2/docs/OWED.md:32 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L32).

[^s13]: [fn: fn2/docs/OWED.md:33 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L33).

[^s14]: [fn: fn2/docs/OWED.md:21 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L21).

[^s15]: [fn: fn2/docs/design/RELEASE-PLAN.md:251 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/RELEASE-PLAN.md#L251).

[^s16]: [fn: fn2/docs/OWED.md:30 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L30).

[^s17]: [:doc defthm]

[^s18]: [:doc assert-event]

[^s19]: [example: examples/assured/owed.lisp] [Source](../../examples/assured/owed.lisp).

[^s20]: [example: examples/assured/ownership.lisp] [Source](../../examples/assured/ownership.lisp).

[^s21]: [guide: humans/06-process.md:113] [Source](../../humans/06-process.md).

[^s22]: [guide: fn-lessons/23-teeth.md:61] [Source](../../fn-lessons/23-teeth.md).

[^s23]: [fn: fn2/books/reference.lisp:248 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L248).

[^s24]: [fn: fn2/books/reference.lisp:92 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L92).

[^s25]: [fn: fn2/books/reference.lisp:142 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L142).

[^s26]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:87 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L87).

[^s27]: [fn: fn2/books/reference.lisp:254 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L254).

[^s28]: [fn: fn2/docs/design/EXECUTION-MODEL.md:27 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/EXECUTION-MODEL.md#L27).

[^s29]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:56 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L56).

[^s30]: [example: examples/assured/square-paste.lisp] [Source](../../examples/assured/square-paste.lisp).

[^s31]: [:doc lemma-instance]

[^s32]: [fn: fn2/docs/design/DSL-METATHEORY.md:32 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L32).

[^s33]: [fn: fn2/docs/design/DSL-METATHEORY.md:34 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L34).

[^s34]: [fn: fn2/docs/design/DSL-METATHEORY.md:544 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L544).

[^s35]: [fn: fn2/docs/design/DSL-METATHEORY.md:559 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L559).

[^s36]: [fn: fn2/docs/design/COHERENCE.md:862 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L862).

[^s37]: [fn: fn2/docs/design/LEAN-METATHEORY.md:211 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L211).

[^s38]: [fn: fn2/docs/design/LEAN-METATHEORY.md:215 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L215).

[^s39]: [fn: fn2/docs/design/LEAN-METATHEORY.md:216 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L216).

[^s40]: [fn: fn2/docs/design/LEAN-METATHEORY.md:217 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L217).

[^s41]: [fn: fn2/docs/design/LEAN-METATHEORY.md:218 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L218).

[^s42]: [fn: fn2/docs/design/COHERENCE.md:855 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L855).

[^s43]: [fn: fn2/docs/design/COHERENCE.md:860 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L860).

[^s44]: [fn: fn2/experiments/squares/E1-RESULTS.md:14-98 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L14).

[^s45]: [fn: fn2/experiments/squares/E2-RESULTS.md:1-28 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L1).

[^s46]: [fn: fn2/experiments/squares/E2-RESULTS.md:151-168 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L151).

[^s47]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:9 @worktree, read 2026-10-29]

[^s48]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:11 @worktree, read 2026-10-29]

[^s49]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read 2026-10-29]

[^s50]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:15 @worktree, read 2026-10-29]

[^s51]: [example: examples/assured/nth-cost.lisp] [Source](../../examples/assured/nth-cost.lisp).

[^s52]: [fn: fn2/docs/design/TRANSPORT.md:548 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/TRANSPORT.md#L548).

[^s53]: [example: examples/transport/cursor-iso.lisp] [Source](../../examples/transport/cursor-iso.lisp).

[^s54]: [fn: fn2/docs/design/TRANSPORT.md:555 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/TRANSPORT.md#L555).

[^s55]: [fn: fn2/docs/design/TRANSPORT.md:566 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/TRANSPORT.md#L566).

[^s56]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:8 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L8).

[^s57]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:132 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L132).

[^s58]: [guide: fn-lessons/06-the-apparatus.md:64] [Source](../../fn-lessons/06-the-apparatus.md).

[^s59]: [fn: fn2/docs/design/TRANSPORT.md:442 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/TRANSPORT.md#L442).

[^s60]: [fn: fn2/docs/design/LEAN-METATHEORY.md:179 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L179).

[^s61]: [fn: fn2/docs/design/COHERENCE.md:42 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L42).

[^s62]: [fn: fn2/docs/design/COHERENCE.md:810 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L810).

[^s63]: [fn: fn2/docs/design/COHERENCE.md:130 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L130).

[^s64]: [fn: fn2/docs/design/LEAN-METATHEORY.md:132 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L132).

[^s65]: [fn: fn2/docs/design/LEAN-METATHEORY.md:183 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L183).

[^s66]: [fn: fn2/docs/design/LEAN-METATHEORY.md:146 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L146).

[^s67]: [fn: fn2/docs/design/COHERENCE.md:815 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L815).

[^s68]: [fn: fn2/docs/design/COHERENCE.md:813 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L813).

[^s69]: [fn: fn2/docs/design/COHERENCE.md:817 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L817).

[^s70]: [example: examples/assured/summary-upto.lisp] [Source](../../examples/assured/summary-upto.lisp).

[^s71]: [fn: fn2/docs/design/COHERENCE.md:814 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L814).

[^s72]: [fn: fn2/docs/design/RELEASE-PLAN.md:279 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/RELEASE-PLAN.md#L279).

[^s73]: [fn: fn2/docs/design/DSL-METATHEORY.md:594 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L594).

[^s74]: [fn: fn2/docs/design/RELEASE-PLAN.md:213 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/RELEASE-PLAN.md#L213).
