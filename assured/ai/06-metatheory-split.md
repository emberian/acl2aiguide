# assured/ai/06. The metatheory split: Lean for frame theorems, ACL2 for instances

Load when exporting ACL2 declarations to Lean, composing instance proofs, or auditing the bridge. Companion: [The metatheory split](../humans/06-metatheory-split.md).
Keep the pins distinct: ACL2 `127f7b877`; Lean `dddc32d34`; that Lean export labels its ACL2 source `origin/fn2/main 137695dfc`.
[fn: fn2/meta/Fn2/Instances/LayerA.lean:1-6 @dddc32d34]
[fn: fn2/meta/Fn2/Instances/LayerA.lean:771 @dddc32d34]

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| Generated behavior changes; exported model stays unchanged | Table-only export omits admitted bodies. [fn: fn2/docs/design/LEAN-METATHEORY.md:169-175 @66ff84f4a, read 2026-10-29] | 7 |
| A row is reported as a proof | Declaration, executable check and theorem admission conflated. [fn: fn2/docs/design/LEAN-METATHEORY.md:128-148 @66ff84f4a, read 2026-10-29] | 2 |
| Catalogue cases compose, but an executed case escapes | Coverage premise missing. [fn: fn2/meta/Fn2/Coherence.lean:489-510 @dddc32d34] | 3 |
| Actions on different machines do not commute | Shared allocator state invalidates independence. [fn: fn2/meta/Fn2/Coherence.lean:342-417 @dddc32d34] | 4 |
| Q1 licence is reported as Q1 proved | Per-case squares remain hypotheses. [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:51-64 @dddc32d34] | 5 |
| Matching theorem name hides a different statement | Exact formula binding missing. [fn: fn2/docs/design/DSL-METATHEORY.md:513 @66ff84f4a, read 2026-10-29] | 6 |
| Reviewed Lean fails elaboration | Reading substituted for a build. [fn: fn2/docs/design/LEAN-METATHEORY.md:200-205 @66ff84f4a, read 2026-10-29] | 8 |

## 1. Assign the obligation by subject

- Do not move a named machine's theorem to Lean because it quantifies over every execution. Keep its code, guards, representation relation and arithmetic in ACL2.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:44-49 @66ff84f4a, read 2026-10-29]
- Assign named-function and concrete-converter proofs to ACL2; parameterized presentation and diagram theorems to Lean; exported-subject fidelity to the bridge; physical execution and eventual progress to explicit environmental models and evidence.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:44-57 @66ff84f4a, read 2026-10-29]
- Treat this as an engineering split. ACL2 can encode presentations and diagrams as data; the fn2 choice puts the frame in Lean with Mathlib and instance proofs beside the ACL2 implementation.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:25 @66ff84f4a, read 2026-10-29]

## 2. Keep declarations, checks and proofs distinct

- Never promote table membership to theorem admission. The manual: "By convention, no user-defined table is important to ACL2's soundness."
  [:doc table]
- Record declarations where artifacts are generated. Qualify identities: fn2 emits a machine and a columns table with the same bare name; `ids_qualified` checks qualified uniqueness.
  [fn: fn2/books/machines.lisp:203-241 @127f7b877]
  [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:25-28 @dddc32d34]
- Keep `defthm-owed` owed: fn2 defines a `$OWED` function and records the source formula, variables, teeth and status; it admits no theorem asserting that formula.
  [fn: fn2/books/owed.lisp:11-22 @127f7b877]
- Use separate evaluating teeth. The manual describes `defun-nx` as "Define a non-executable function symbol"; its calls "cannot be evaluated." fn2 requires named zero-argument teeth.
  [:doc defun-nx] [fn: fn2/books/owed.lisp:29-49 @127f7b877]
- Require exactly `t` from a tooth. `assert-event` alone checks for "a non-`nil` value, causing an error otherwise"; fn2 uses `(equal (tooth) t)`. Passing leaves the obligation owed.
  [:doc assert-event] [fn: fn2/docs/OWED.md:3-8 @127f7b877]
- Copy these forms in `owed.lisp`'s context: `defthm-claimed` admits a theorem and records `:proved`; `defthm-owed` translates the statement and runs teeth. Derive counts from the table.
  [example: examples/assured/owed.lisp]

```lisp
(defthm-claimed sat-inc-bounded
  (implies (natp x) (<= (sat-inc x) (max x *sat-max*))))

(defun sat-run-teeth ()
  (declare (xargs :guard t))
  (and (equal (sat-run 250 10) 255)                ; positive: saturates
       (< (wrap-inc 255) 255)                       ; negative: the sibling wraps
       t))

(defthm-owed sat-run-monotone (x n)
  (implies (and (natp x) (natp n)) (<= x (sat-run x n)))
  :teeth (sat-run-teeth))

(assert-event (equal (claim-counts (w state)) '(1 1)))
```

## 3. Supply squares and coverage before composing

- Do not infer a simulation from categorical terminology. `Sq` requires a successful source transition from related states to have a successful target transition ending in related states.
  [fn: fn2/meta/Fn2/Square.lean:79-83 @dddc32d34]
- Use `Sq.seq` along transitions and `Sq.stack` along representation relations; use `Sq.idLoose` and `Sq.idTight` for identities.
  [fn: fn2/meta/Fn2/Square.lean:97-147 @dddc32d34]
- Do not claim a framed double category. The implemented `restrict` is a weakest precondition on an input pair; its documentation withdraws the cartesian-lift claim for partial transitions.
  [fn: fn2/meta/Fn2/Square.lean:85-95 @dddc32d34]
- Apply `Sq.paste` after supplying a square per label; a source label may expand to a finite target word. For `Sq.paste_cover`, establish that every executed label belongs to the covered catalogue.
  [fn: fn2/meta/Fn2/Square.lean:172-205 @dddc32d34]
- Keep the coverage counterexample: `uncovered_catalogue_holds` covers `false`; `uncovered_case_fails` uses `true`. Catalogue enumeration does not establish execution coverage.
  [fn: fn2/meta/Fn2/Coherence.lean:489-510 @dddc32d34]

## 4. Demand witnesses, teeth and restricted conclusions

- Do not infer independence from different machine names. The accept/close toy shares an allocator: with no free row and one outstanding close, accept-then-close admits zero connections; the reverse admits one.
  [fn: fn2/meta/Fn2/Coherence.lean:342-417 @dddc32d34]
  [fn: fn2/meta/Fn2/Coherence.lean:438-447 @dddc32d34]
- Supply `coherence` with G1 squares and observation agreement, implementation diamonds, a G0-related start, trace-equivalent words and a successful implementation run. Claim a successful reference run with equal observations, not completion of arbitrary schedules.
  [fn: fn2/meta/Fn2/Coherence.lean:97-119 @dddc32d34]
- Do not infer enabledness preservation from `Diamonds`: equal two-step partial runs can both fail. `TraceEq` connects words by adjacent swaps of declared-independent labels.
  [fn: fn2/meta/Fn2/Coherence.lean:59-82 @dddc32d34]
- Use `IndependentDiamonds` when enabledness matters. Establish footprint respect and absence of write/read or write/write conflicts; empty declarations do not excuse actual writes.
  [fn: fn2/meta/Fn2/Coherence.lean:138-150 @dddc32d34]
  [fn: fn2/meta/Fn2/Coherence.lean:190-235 @dddc32d34]
- Pair `twoRecv_coherence_witness` with `acceptClose_without_g2`. The latter retains the other coherence premises while falsifying the conclusion: copy that shape for hypothesis-removal tests.
  [fn: fn2/meta/Fn2/Coherence.lean:292-338 @dddc32d34]
  [fn: fn2/meta/Fn2/Coherence.lean:449-487 @dddc32d34]
- Restrict `conservative` to run behavior. Its `Extension` supplies projection, label translation, converter, revised-label squares and base-event lifting; it is not a theorem about syntactic derivability or model expansion.
  [fn: fn2/meta/Fn2/Conservative.lean:11-17 @dddc32d34]
  [fn: fn2/meta/Fn2/Conservative.lean:33-43 @dddc32d34]
  [fn: fn2/meta/Fn2/Conservative.lean:80-122 @dddc32d34]
- Keep `revision_counts` as the witness. Treat `badRevision_breaks_counts` and `badRevision_annotate_not_square` as separate theorems, not a packaged hypothesis-removal statement.
  [fn: fn2/meta/Fn2/Conservative.lean:199-220 @dddc32d34]
- Restrict parametricity clients to commands, interface observations and results. Supply related initial states, command preservation and equal observations for `abstraction`; no representation-reading operation belongs to `Client`.
  [fn: fn2/meta/Fn2/Param.lean:28-64 @dddc32d34]
- Check `counter_doubled_clients`, `peek_breaks_abstraction` and `drop_exec_breaks`. Establish the ACL2 interface restriction and primitive correspondence; an "abstract" registry label supplies neither.
  [fn: fn2/meta/Fn2/Param.lean:73-138 @dddc32d34]

## 5. Generate presentation data; retain instance obligations

- Avoid a hand-maintained second specification. Generate the Lean presentation through the implemented path:
  [fn: fn2/meta/emit/print-registry.lsp:7-25 @dddc32d34]
  [fn: fn2/meta/emit/emit.sh:12-16 @dddc32d34]

```text
ACL2 world tables
  -> print-registry.lsp
  -> registry.sexp
  -> emit_lean.py
  -> Fn2/Instances/LayerA.lean
```

- Reject unknown or missing consumed keys; distinguish explicitly omitted keys. Keep capacities, initializers and formulas as `Opaque` text: this exporter does not translate formulas into Lean propositions.
  [fn: fn2/meta/emit/emit_lean.py:124-128 @dddc32d34]
  [fn: fn2/meta/emit/emit_lean.py:205-234 @dddc32d34]
  [fn: fn2/meta/emit/emit_lean.py:271-282 @dddc32d34]
- Read `registry_wf` as recorded-row and cross-row consistency. Do not infer omitted behavior or initializer semantics. Keep handwritten `nonRegistryCases` distinct from emitted cases.
  [fn: fn2/meta/Fn2/Decl.lean:159-188 @dddc32d34]
  [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:22-23 @dddc32d34]
  [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:35-44 @dddc32d34]
- Read `q1_licensed` as this implication, in ASCII notation; the catalogue supplies no per-case proofs:
  [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:60-64 @dddc32d34]

```text
Given:
  for every c in q1Cases,
    Sq R (stepA c) (run stepB (h c)) R

Conclude:
  for every word w whose labels belong to q1Cases,
    Sq R (run stepA w) (run stepB (expand h w)) R
```

- For fn2's proposed Q1 decomposition, normalize reference work counters in the intermediate relation. Raw core equality mismatches concrete per-transition accounting and reference counters carried until exit.
  [fn: fn2/docs/design/DSL-METATHEORY.md:252-261 @66ff84f4a, read 2026-10-29]
- Retain entry, exit, termination, selector coverage and accounting obligations. Preserve the exported refinement statement's status/count equality, resulting-core well-formedness, representation relation and action/work bounds.
  [fn: fn2/docs/design/DSL-METATHEORY.md:277 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/OWED.md:33 @127f7b877]

## 6. Bind the bridge to subjects and statements

- Do not bind an admitted theorem by name alone. Keep source and translated formulas; account for the owed wrapper. fn2's bridge is incomplete here: `defthm-owed` stores the untranslated formula.
  [fn: fn2/books/owed.lisp:11-20 @127f7b877]
  [fn: fn2/docs/design/DSL-METATHEORY.md:513 @66ff84f4a, read 2026-10-29]
- Inspect every clause of the bridge assumption:
  [fn: fn2/docs/design/LEAN-METATHEORY.md:158 @66ff84f4a, read 2026-10-29]

| Clause | Establish correspondence |
| --- | --- |
| Identity | Qualified names designate the same declarations, functions and events |
| Payload | Values and order survive; unsupported payloads are explicit |
| Artifact | Exported subjects are the artifacts actually admitted, including assembly outputs |
| Obligation | Catalogue cases bind intended statements; catalogue existence does not establish coverage |
| Semantic | Interpreted Lean premises express the ACL2 formulas' properties |
| Evidence | Proof/check records concern the same subjects at the same revisions |

- Retain owner/case identity, contract/boundary, endpoints, formals/calling convention, both formulas, proof reference, check scope and dependencies. Reject a proposed realization with an additional unestablished hypothesis.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:144 @66ff84f4a, read 2026-10-29]
- Keep finite-check premises owed. No ACL2 proof object enters Lean and no status row generates a Lean axiom. Compose covered trajectories whose intermediate states and contracts join; matching seed numbers do not suffice.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:142-146 @66ff84f4a, read 2026-10-29]
- Do not treat the bridge assumption as replacing kernel or execution trust; opaque formulas do not discharge semantic correspondence.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:158-179 @66ff84f4a, read 2026-10-29]

## 7. Test captured payload, rejected payload and invisible behavior

- Separate mutation outcomes. The row-only mutant failed ACL2's router guard proof; its later proof-free export is diagnostic evidence. The deadline-width mutant certified and changed payload without failing a pinned Lean control.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:164-165 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/LEAN-METATHEORY.md:167 @66ff84f4a, read 2026-10-29]
- Preserve the measured limit: the retired-behavior mutant certified, its registry was byte-identical, and its emitted model had a zero-line diff. This refutes table-only artifact fidelity, not Lean's theorems about that presentation.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:171-175 @66ff84f4a, read 2026-10-29]
- Bind generated names to admitted bodies in a `:generated` manifest with fingerprints. Record producer, emitting section and signatures, including assembly outputs.
  [fn: fn2/docs/design/DSL-METATHEORY.md:145-158 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/DSL-METATHEORY.md:504 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/LEAN-METATHEORY.md:173-175 @66ff84f4a, read 2026-10-29]
- Copy these assertions in `registry-emit.lisp`'s context. Its body manifest distinguishes the generators where the table-only export cannot. A changed fingerprint does not prove correctness.
  [example: examples/assured/registry-emit.lisp]

```lisp
(assert-event (equal (export-row 'echo-v1 (w state))
                     (export-row 'echo-v2 (w state))))

(assert-event (equal (echo-v1-observes-p 2 :send-result) nil))
(assert-event (equal (echo-v2-observes-p 2 :send-result) t))

(assert-event (not (equal (export-row-with-bodies 'echo-v1 (w state))
                          (export-row-with-bodies 'echo-v2 (w state)))))
```

- Distinguish the later E2 pass 3 result from this earlier Lean export.
  One public `defsquare` form served Q1 and Q4 through specialized statement
  templates. Require every function named by a role to occur in its
  translated statement, or record an exact unused-role exception. This is
  syntactic binding, not semantic correctness; retain proof-formula equality
  checks and semantic negative controls.
  [fn: fn2/experiments/squares/E2-RESULTS.md:74-115 @d42d18c33]
- Keep E2's statuses separate: 45 rows, 40 owed Q1 and five proved Q4;
  83 evidence records. Fresh ORIGINAL campaigns completed 10,004 G1 checks
  across 19/39 cases, leaving 20 unexercised. The 14 books passed local
  certification below 60 seconds each; these are E2 package results.
  [fn: fn2/experiments/squares/E2-RESULTS.md:1-28 @d42d18c33]
- Charge all support: E2 used 2,085 physical source lines, 1,454 new and
  631 copied. Fourteen were wrapped consumer declarations and 2,071 were
  other source. No implemented manual-registration baseline established
  net savings. Shared-handler defects still need independent client oracles.
  [fn: fn2/experiments/squares/E2-RESULTS.md:151-168 @d42d18c33]
  [fn: fn2/experiments/squares/E2-RESULTS.md:18-23 @d42d18c33]

## 8. Build and report only the assurance obtained

- Do not substitute review for elaboration. Run the recorded commands from `fn2/meta`; keep build, axiom census, export freshness and instance bindings separate.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:193-198 @66ff84f4a, read 2026-10-29]
  [fn: fn2/docs/design/LEAN-METATHEORY.md:215 @66ff84f4a, read 2026-10-29]

```sh
lake build
lake env lean AxiomCensus.lean
```

- For the recorded failures: expose concrete carriers through abbreviations; give concealed-carrier arithmetic binders explicit `Nat` types; rewrite with the step hypothesis before simplification unfolds the accept/close step.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:200-203 @66ff84f4a, read 2026-10-29]
- Withdraw a failed proof claim even when Lean is not a first-release shipping prerequisite. Keep admitted theorems, translated owed rows and passing checks distinct.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:215 @66ff84f4a, read 2026-10-29]
- Do not claim ACL2 soundness, opaque-formula truth, universal validity from bounded checks, or durability, fairness and environmental integrity from simulation squares.
  [fn: fn2/docs/design/LEAN-METATHEORY.md:177-179 @66ff84f4a, read 2026-10-29]
- Do not claim frame completeness. Coherence covers routes already connected by declared swaps; it does not establish that every intended interchangeable pair is connected.
  [fn: fn2/meta/Fn2/Coherence.lean:111-119 @dddc32d34]
  [fn: fn2/docs/design/COHERENCE.md:291-303 @66ff84f4a, read 2026-10-29]
