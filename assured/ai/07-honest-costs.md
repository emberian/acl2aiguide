# assured/ai/07. Honest costs: proved, owed, and outside the result

Load when reporting proof status, estimating framework work, or claiming
refinement, transport, or performance benefits. Twin of
`assured/humans/07-honest-costs.md`. Copy forms with their cited book's
definitions in scope. Preserve revision pins and dated `@worktree` citations.

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| Certified book advertised as universal proof | Owed formulas can survive certification while false. [example: examples/assured/owed.lisp] | 2 |
| Theorem count advertised as discharged guarantees | Source forms and generated events differ from ledger obligations. [fn: fn2/books/columns.lisp:493 @127f7b877] | 1 |
| Turn refinement advertised as server correctness | Reference shares implementation handlers. [fn: fn2/books/reference.lisp:92 @127f7b877] | 3 |
| Generic composition advertised as completed instances | Concrete substitutions generate proof obligations. [:doc lemma-instance] | 3 |
| Estimates summed into a delivery total | DSL and experiment deliverables overlap. [fn: build/coordinator/fn2/DSL-METATHEORY.md:559 @worktree, read 2026-10-29] | 4 |
| Small step count hides expensive certification | Generic `nth` rules increase elapsed proof cost. [example: examples/assured/nth-cost.lisp] | 5 |
| Generated lines advertised as work saved | Toy transport required 72 handwritten lines for 71 generated statement/definition lines. [fn: build/coordinator/fn2/TRANSPORT.md:548 @worktree, read 2026-10-29] | 5 |
| Framework size omitted from the bill | Harness includes maintained judgments and generated inventories. [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:132 @worktree, read 2026-10-29] | 6 |
| Bounded agreement advertised as universal correctness | Checked ACL2 rows remain owed. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:146 @worktree, read 2026-10-29] | 7 |

## 1. Count statements separately from proofs

- Do not count an owed declaration as theorem admission. The pinned
  `defthm-owed` defines a non-executable statement function and records
  `:status :owed`; its expansion contains no `defthm`.
  [fn: fn2/books/owed.lisp:11 @127f7b877]
- Report the checked-in export at `127f7b877` as **22 rows, 22 owed, 0 proved**.
  Preserve the measurement's scope: this command does not rerun the exporter.
  [measured: `git -C ~/dev/fn show 127f7b877:fn2/docs/OWED.md | awk '/^\| `/{rows++; if ($0 ~ /\| :OWED \|/) owed++; if ($0 ~ /\| :PROVED \|/) proved++} END {print rows, owed+0, proved+0}'`, output `22 22 0`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]
- Label **236** as column-zero source forms; indented forms and macro
  expansions are outside this inventory.
  [measured: `git -C ~/dev/fn grep -h -E '^\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `236`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]
- Label **340** as source occurrences allowing indentation, including
  generator templates. Neither grep counts expanded events or guarantees.
  [measured: `git -C ~/dev/fn grep -h -E '^[[:space:]]*\(defthmd?[[:space:]]' 127f7b877 -- fn2/books fn2/sim | wc -l`, output `340`; macOS arm64 laptop, 2026-10-29; ACL2 8.7 project, ACL2 not invoked]
  [fn: fn2/books/columns.lisp:493 @127f7b877]
  [fn: fn2/books/columns.lisp:539 @127f7b877]
- Prefer the pinned export over the release plan's stale "Twenty-one"
  sentence: the export includes the ninth issue refusal, entropy.
  [fn: build/coordinator/fn2/RELEASE-PLAN.md:251 @worktree, read 2026-10-29]
  [fn: fn2/docs/OWED.md:30 @127f7b877]

## 2. Keep passing teeth distinct from admitted theorems

- Do not promote certification or evaluation into proof. The manual calls
  `defthm` "Prove and name a theorem"; `assert-event` checks that evaluation
  "returns a non-`nil` value, causing an error otherwise". [:doc defthm]
  [:doc assert-event]
- Read this example's ledger from the world: `defthm-claimed` emits a theorem
  and proved row; `defthm-owed` translates the formula, evaluates teeth, and
  records an owed row. The count below is `(proved owed)`.
  [example: examples/assured/owed.lisp]

```lisp
(defthm-claimed sat-inc-bounded
  (implies (natp x) (<= (sat-inc x) (max x *sat-max*))))

(defthm-owed sat-run-monotone (x n)
  (implies (and (natp x) (natp n)) (<= x (sat-run x n)))
  :teeth (sat-run-teeth))

(assert-event (equal (claim-counts (w state)) '(1 1)))
```

- Search beyond the teeth's saturation and wrapping cases. At `x = 256`,
  `n = 1`, the owed conclusion is false: `256 <= 255`. Copy the proved
  witness, not a claim that failed proof search found a counterexample.
  [example: examples/assured/owed.lisp]
  [guide: humans/06-process.md:113]

```lisp
(defthm sat-run-monotone-false-at-256
  (not (<= 256 (sat-run 256 1))))
```

- Hunt empty sets, zero, and values outside the intended type first.
  [guide: fn-lessons/23-teeth.md:61]
- Keep small-pool proofs scoped to the example. `slot-free-stale`,
  `slot-free-refuses-borrowed`, and `slot-free-generation-monotone` do not
  discharge fn2's pool obligations. Its demonstration checks this sequence:
  [example: examples/assured/ownership.lisp]
  [fn: fn2/docs/OWED.md:12 @127f7b877]

```lisp
(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
```

## 3. Read the refinement statement and pay for each instance

- Do not expand `fn2-turn-refinement` into server correctness. Its scope is
  "Owed refinement to independent list selection, observation ordering and
  budget accounting; shared bounded machine semantics, no fusion."
  [fn: fn2/books/reference.lisp:248 @127f7b877]
- Audit shared handlers: harvest, observations, machine execution, clock
  update, and service operations can preserve the same defect on both sides.
  [fn: fn2/books/reference.lisp:92 @127f7b877]
  [fn: fn2/books/reference.lisp:142 @127f7b877]
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]
- Keep status/counter agreement, recognizers, representation relation, and
  action/work bounds separate from measured CPU cost. The owed inequality's
  `24` and `4129` are self-declared constants.
  [fn: fn2/books/reference.lisp:254 @127f7b877]
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]
- Retain the larger execution contract: boundary compatibility, initialization,
  semantic invariants, outputs/effects, resumable progress, fusion, and crash
  composition over every submitted-action prefix and death cut remain outside
  what the present owed turn statement discharges.
  [fn: build/coordinator/fn2/EXECUTION-MODEL.md:27 @worktree, read 2026-10-29]
- Do not treat generic pasting as ACL2 instance evidence: the pinned Lean
  theorem's catalogue-case squares remain premises.
  [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:56 @dddc32d34]
- Pay the concrete obligations: "before such a lemma instance can be used,
  the system will generate proof obligations". [:doc lemma-instance]
- Follow the completed example: `fused-refines-reference` uses `sq-paste-obs`
  after step and observation lemmas. Preserve the mutant witness too.
  [example: examples/assured/square-paste.lisp]

```lisp
(defthm fused-step-bad-breaks-square
  (let ((a (fused-init)) (b (ref-init)) (l '(:recv2 1 5 7)))
    (and (fused-rel a b)
         (not (fused-rel (fused-step-bad a l) (ref-run b (fused-h l)))))))
```

## 4. Quote estimates with scope; reconcile overlaps before adding

- Do not report a named generator as completed proof work. The DSL proposal
  "proves nothing by itself"; it states obligations, enumerates cases, and exposes gaps.
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:32 @worktree, read 2026-10-29]
- Quote **13 engineer-days pessimistically for DM0a, DM1, DM0b**: identities
  and manifest, obligation storage, callbacks, staging, and seals. These are
  part of the larger plan.
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:34 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:544 @worktree, read 2026-10-29]
- Quote **100 engineer-days pessimistically for mandatory metatheory packages**,
  excluding R5e, R6a, R6b, R7 and experiment replay/campaign work. Reconcile DM3's
  overlapping experiment deliverables before adding budgets.
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:559 @worktree, read 2026-10-29]
- Quote **12 engineer-days plus several machine-days pessimistically for the
  replay experiment**: choices/replay, correspondence/comparison, mutation controls,
  enumeration/measurement; exclude generic recursive checkpoints, partial-order
  reduction, and a universal declaration form.
  [fn: build/coordinator/fn2/COHERENCE.md:862 @worktree, read 2026-10-29]
- Keep Lean's pessimistic estimates separate from elapsed work; its bridge overlaps DSL work.
  [fn: build/coordinator/fn2/LEAN-METATHEORY.md:211 @worktree, read 2026-10-29]

| Pessimistic estimate | Scope |
| --- | --- |
| 2 engineer-days | Advisory freshness, theorem status, bindings, named failures. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:215 @worktree, read 2026-10-29] |
| 8 engineer-days | Qualified foundation, proposed mixed pasting and toy completeness. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:216 @worktree, read 2026-10-29] |
| 7 engineer-days | Exact statement binding and artifact provenance, inside/beside DM0a/DM1. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:217 @worktree, read 2026-10-29] |
| 5 engineer-days | B emitter: tables, identity/order checks, deterministic serialization. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:218 @worktree, read 2026-10-29] |

## 5. Measure proof time and handwritten work

- When generated preservation proofs become expensive, derive the accessor API
  using generic numeric-array facts, then disable broad rules and retain
  field-specific facts. W1 repaired matching against unrelated fields.
  [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read 2026-10-29]
- Label W1's **1,876.11 s -> 284.41 s** as summed certification times with two
  laptop jobs, not wall-clock build duration. The repair at `1fa1fe24b` compares
  60 original books with 72 final books after assembly splitting.
  [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:9 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:11 @worktree, read 2026-10-29]
- Measure elapsed proof cost alongside steps. Published laptop measurements
  (ACL2 8.7, SBCL 2.6.8, 2026-10-29) prove the same bound with both rule sets.
  [example: examples/assured/nth-cost.lisp]

| Fields | Specific only | Specific and generic |
| ---: | ---: | ---: |
| 12 | 0.00 s; 1,164 steps | 0.04 s; 1,659 steps |
| 24 | 0.01 s; 2,292 steps | 0.50 s; 3,879 steps |
| 36 | 0.02 s; 3,420 steps | 2.07 s; 6,675 steps |

- Copy the example's disabling form and field-specific proof.
  [example: examples/assured/nth-cost.lisp]

```lisp
(nc-generic nil 24)

(defthm field-sum-bound-specific
  (nc-field-sum-bound 24)
  :rule-classes nil)
```

- Report Experiment B's **72 handwritten lines for 71 generated statement/
  definition lines**. Do not call its 1,242 printed expansion lines work saved.
  [fn: build/coordinator/fn2/TRANSPORT.md:548 @worktree, read 2026-10-29]
- Account for handwritten bases, maps, and correspondence proofs before
  `propagate-iso`; transport is demonstrated, fn2-scale source savings remain unmeasured.
  [example: examples/transport/cursor-iso.lisp]
  [fn: build/coordinator/fn2/TRANSPORT.md:555 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29]

## 6. Include the apparatus in the bill

- Do not omit harness maintenance. H2 reports about 210,000 added lines against
  a core of about 10,000 at harness revision `5b641fc0a`; retain that approximate,
  historical scope instead of attributing the count to `127f7b877`.
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:8 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:132 @worktree, read 2026-10-29]
- Name each checker's contract and defect class found. Use schema-checked judgment
  data and build outputs for generated inventories.
  [guide: fn-lessons/06-the-apparatus.md:64]
  [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:132 @worktree, read 2026-10-29]
- Budget manifests, bridges, serializers, reports, retention, dependency identity,
  activation, recovery, compatibility, and resource accounting.
  [fn: build/coordinator/fn2/TRANSPORT.md:442 @worktree, read 2026-10-29]

## 7. Preserve the boundary of the result

- Do not promote a typed registry row into claims outside composition.
  [fn: build/coordinator/fn2/LEAN-METATHEORY.md:179 @worktree, read 2026-10-29]

| Boundary | Keep outside the claim |
| --- | --- |
| Environment | X rows are containment assumptions; native experiments do not prove all native behavior contained. [fn: build/coordinator/fn2/COHERENCE.md:42 @worktree, read 2026-10-29] [fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29] |
| Liveness | Finite-prefix agreement does not establish eventual replies; scheduler opportunity is not machine completion. [fn: build/coordinator/fn2/COHERENCE.md:130 @worktree, read 2026-10-29] [fn: fn2/docs/OWED.md:21 @127f7b877] |
| Generator completeness | Sound pasting covers supplied diagrams; frame completeness remains unestablished. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:132 @worktree, read 2026-10-29] [fn: build/coordinator/fn2/LEAN-METATHEORY.md:183 @worktree, read 2026-10-29] |
| Bounded checks | Checked rows stay owed; covered runs need composing states and contracts. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:146 @worktree, read 2026-10-29] |
| Independent semantics | Shared handlers leave OWN, client oracles, and semantic contracts independent work. [fn: build/coordinator/fn2/COHERENCE.md:815 @worktree, read 2026-10-29] |
| Speed and parallelism | Replay/comparison can consume savings; scheduler and allocator effects constrain independence. [fn: build/coordinator/fn2/COHERENCE.md:813 @worktree, read 2026-10-29] [fn: build/coordinator/fn2/COHERENCE.md:817 @worktree, read 2026-10-29] |
| Toy transport | A does not establish storage history; B does not connect logical rows to served columns. [fn: build/coordinator/fn2/TRANSPORT.md:566 @worktree, read 2026-10-29] |

- Claim observation agreement at the proved boundary. `par-summary-adequate`
  proves parity agreement after every suffix; this assertion checks parity `1`
  and summary steps `5`, not representation equality.
  [example: examples/assured/summary-upto.lisp]

```lisp
(assert-event
 (let ((j '(:inc :noop :inc :inc :noop)))
   (and (equal (par-s-obs (par-s-fold (par-conv nil) j) :parity) 1)
        (equal (par-h-obs (par-h-fold nil j) :parity) 1)
        (equal (cdr (par-s-fold (par-conv nil) j)) 5))))
```

- Allow the replay experiment to lose against equally instrumented sampling;
  include replay, checking, and garbage collection. Its fn2 payoff is unmeasured.
  [fn: build/coordinator/fn2/COHERENCE.md:855 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/COHERENCE.md:860 @worktree, read 2026-10-29]
- Publish performance without making it a performance gate under this policy;
  retain the separate W13 resource guardrail gate.
  [fn: build/coordinator/fn2/COHERENCE.md:814 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/RELEASE-PLAN.md:279 @worktree, read 2026-10-29]
- Report estimate scope, measurement revision/toolchain/domain, proof status,
  and check coverage separately. Record an expired proof budget as an unproved
  obligation with diagnostics, not a counterexample.
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:559 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/DSL-METATHEORY.md:594 @worktree, read 2026-10-29]
  [fn: build/coordinator/fn2/RELEASE-PLAN.md:213 @worktree, read 2026-10-29]