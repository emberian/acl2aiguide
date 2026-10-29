# 6. The metatheory split: Lean for frame theorems, ACL2 for instances

A green Lean build can describe yesterday's registry while today's generated
behavior has changed. In fn2's mutation experiment, removing the retired-phase
exclusion from an observation predicate left the printed registry byte-identical.
The emitted Lean model therefore stayed unchanged. This is the first boundary to
understand: reading declaration tables does not establish fidelity to generated
function bodies. [fn: build/coordinator/fn2/LEAN-METATHEORY.md:169-175 @worktree, read 2026-10-29]

A second boundary is logical: a theorem saying that local squares compose does
not supply those squares. A third is evidential: a translated ACL2 statement,
a passing executable check, an admitted ACL2 theorem and a Lean theorem retain
different statuses. No proof-status row becomes an axiom on the other side.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:128-148 @worktree, read 2026-10-29]

This chapter reads the ACL2 books at `127f7b877` and the Lean project at
`dddc32d34`. The generated `LayerA.lean` in that Lean revision labels its source
`origin/fn2/main 137695dfc`; its counts and the recorded mutation experiment
belong to that export, not to a newly generated export of `127f7b877`.
[fn: fn2/meta/Fn2/Instances/LayerA.lean:1-6 @dddc32d34]
[fn: fn2/meta/Fn2/Instances/LayerA.lean:771 @dddc32d34]

## 6.1 Classify the obligation by its subject

Moving a difficult ACL2 theorem to Lean because it quantifies over every
execution changes the engineering boundary for the wrong reason. A theorem
about a named machine's executions remains an instance theorem; its code,
guards, representation relation and arithmetic live in the ACL2 world.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:44-49 @worktree, read 2026-10-29]

The working decision rule has four cases:

| Subject | Home | What must be supplied |
|---|---|---|
| Named functions, a concrete representation, a converter or an admitted book | ACL2 | The actual instance statement, including outputs, effects, guards and bounds |
| Declaration presentations, interpretations or diagrams constructed from squares | Lean | A frame theorem parameterized by the instance properties |
| Correspondence between an exported row and its admitted ACL2 subject | The bridge | Identity, statement and artifact fidelity |
| Physical execution, environmental evidence or eventual progress | The relevant execution model and evidence | Explicit adapter, persistence and fairness premises |

[fn: build/coordinator/fn2/LEAN-METATHEORY.md:44-57 @worktree, read 2026-10-29]

This is an engineering division, not a claim that first-order logic cannot
express metatheory. ACL2 could encode presentations and diagrams as data.
The cost would include maintaining that encoding, its induction principles and
the categorical vocabulary. The fn2 decision puts that frame in Lean with
Mathlib and keeps named-function proofs beside the ACL2 implementation.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:25 @worktree, read 2026-10-29]

For an ACL2 user, the practical question is therefore precise: does this
obligation concern the functions in this world, or the construction that combines
arbitrary instances satisfying a stated interface? The first stays in ACL2;
the second can become a reusable Lean implication.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:46-48 @worktree, read 2026-10-29]

## 6.2 Record declarations without manufacturing theorems

A registry becomes misleading when a row's existence is treated as evidence
that its advertised property holds. ACL2's manual gives the intended boundary:
"By convention, no user-defined table is important to ACL2's soundness."
Tables store user data in the world; they are not a second theorem-admission
mechanism. [:doc table]

Record the declaration where the macro generates its artifacts. In fn2,
`fn2-machine-events` emits both `defcolumns` and the machine's functions, then
writes `fn2-machine-kinds`. The row records states, columns, continuations,
observed events and other declaration data. It does not record admitted bodies.
[fn: fn2/books/machines.lisp:203-241 @127f7b877]

Use a qualified identity. The same declaration emits a machine and a columns
table with the same bare name; identifying both by name alone conflates them.
The Lean fact `ids_qualified` checks that qualified identities are unique while
the bare names are not.
[fn: fn2/books/machines.lisp:213 @127f7b877]
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:25-28 @dddc32d34]

An owed statement needs a different treatment from a proved statement.
The actual `defthm-owed` macro defines a `$OWED` function with `defun-nx` and
records the source formula, variables, teeth and `:owed` status. It admits no
theorem asserting that formula.
[fn: fn2/books/owed.lisp:11-22 @127f7b877]

The manual calls `defun-nx` a way to "Define a non-executable function symbol";
it says the resulting calls "cannot be evaluated." The evaluating teeth are
therefore separate functions. fn2 resolves each named tooth, requires zero
arguments and emits an assertion that its result equals `t`.
[:doc defun-nx] [fn: fn2/books/owed.lisp:29-49 @127f7b877]

For the executable check, the manual describes `assert-event` as checking that
evaluation returns "a non-`nil` value, causing an error otherwise." fn2's
`(equal (tooth) t)` form makes the required tooth result exact. That check
remains evidence; the exported obligation remains owed.
[:doc assert-event] [fn: fn2/docs/OWED.md:3-8 @127f7b877]

`examples/assured/owed.lisp` keeps the distinction in a world table: its
`defthm-owed` admits a `defun-nx` of the statement (so a statement naming
an undefined function is refused at once, as the book shows), runs each
named tooth and requires exactly `t`, and records the row as `:owed`; its
`defthm-claimed` is `defthm` plus a `:proved` row; `claim-counts` reads
the table, and the book asserts `(1 1)`. Teeth given as prose are refused
[example: examples/assured/owed.lisp].

## 6.3 What the frame proves

Calling the construction a double category does not make a simulation square
true. A square still requires that a successful source transition from related
states has a successful target transition ending in related states.
That is the content of `Sq`.
[fn: fn2/meta/Fn2/Square.lean:79-83 @dddc32d34]

The construction uses state types as objects, partial transitions as loose
arrows and representation relations as tight arrows. A partial transition
returns an optional next state; absence means the transition is not enabled.
The tight arrows connect to Mathlib's `RelCat`, and `Tight.toRelCat_comp`
identifies their composition with relational composition.
[fn: fn2/meta/Fn2/Square.lean:29-75 @dddc32d34]

`Sq.seq` composes squares along transitions; `Sq.stack` composes them along
representation relations. `Sq.idLoose` and `Sq.idTight` supply the identities.
The squares are propositions, so `Sq.thin` and `Sq.interchange` express the
thinness and interchange law through proof irrelevance.
[fn: fn2/meta/Fn2/Square.lean:97-147 @dddc32d34]

Do not strengthen that description to a framed double category. fn2's earlier
interpretation of `restrict` as a cartesian lift was wrong. The implemented
operation is a weakest precondition on an input pair; its documentation
explicitly withdraws the framing claim for partial transitions.
[fn: fn2/meta/Fn2/Square.lean:85-95 @dddc32d34]

The useful composition theorem is `Sq.paste`: a square for every label gives
a square for every word, allowing a source label to mean a finite target word.
`Sq.paste_cover` adds a catalogue restriction: every label in the run must
belong to the catalogue whose cases have squares.
[fn: fn2/meta/Fn2/Square.lean:172-205 @dddc32d34]

Dropping that coverage premise is unsound. `uncovered_catalogue_holds` proves
the square for the catalogue containing `false`; `uncovered_case_fails` gives
a run using `true` for which the square fails. Enumerating the cases you know
does not prove that every executed case is among them.
[fn: fn2/meta/Fn2/Coherence.lean:489-510 @dddc32d34]

## 6.4 Coherence needs both a witness and a broken sibling

"Different machines" is not an independence theorem. In the accept/close toy,
the listener and an echo connection share the allocator's free count.
With no free row and one outstanding close, accept-then-close admits zero
connections; close-then-accept admits one.
[fn: fn2/meta/Fn2/Coherence.lean:342-417 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:438-447 @dddc32d34]

The theorem `coherence` has a narrower and useful statement. Given a
correspondence containing the G1 step squares and observation agreement,
implementation diamonds, a G0-related start, trace-equivalent words and a
successful implementation run, it supplies a successful reference run with
equal observations. It does not assert that arbitrary schedules complete.
[fn: fn2/meta/Fn2/Coherence.lean:97-119 @dddc32d34]

Here `TraceEq` is generated by adjacent swaps of declared-independent labels.
`Diamonds` requires equal two-step partial runs for each declared pair.
It does not alone establish preservation of enabledness: two actions that
disable one another can have equal failing composite runs.
[fn: fn2/meta/Fn2/Coherence.lean:59-82 @dddc32d34]

`IndependentDiamonds` includes enabledness preservation. The footprint
theorems establish both properties when each action respects its declared
reads and writes and neither writes what the other reads or writes.
Declaring empty footprints while writing anyway is exposed by `liar_indep`,
`liar_not_respects` and `liar_not_diamond`.
[fn: fn2/meta/Fn2/Coherence.lean:138-150 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:190-235 @dddc32d34]

The positive coherence witness is `twoRecv_coherence_witness`: two receive
counters start at zero, the orders are trace-equivalent, both executions
succeed and their observation agrees with a reference total of two.
The G1 squares and observation edge are fields of `sumCorr`.
[fn: fn2/meta/Fn2/Coherence.lean:292-338 @dddc32d34]

The tooth `acceptClose_without_g2` packages every other coherence premise
with failure of the conclusion. Its identity correspondence retains G1 and
observation agreement; the false independence declaration loses G2.
This is the shape to demand of a hypothesis-removal test on the ACL2 side:
retain the other premises and exhibit the failed conclusion.
[fn: fn2/meta/Fn2/Coherence.lean:449-487 @dddc32d34]

## 6.5 Conservativity and parametricity have restricted subjects

A theorem named `conservative` can invite a larger claim than its statement
supports. This one concerns behavior of runs. It does not represent a syntax
of theories, a derivability relation or a model-expansion theorem.
[fn: fn2/meta/Fn2/Conservative.lean:11-17 @dddc32d34]

Its `Extension` certificate supplies a projection, label translation, converter,
a square per revised label and lifting of base events. Under that certificate,
`runs_exactly` identifies base runs with projected and translated revised runs;
`conservative` transports every property of a base word and its final state.
[fn: fn2/meta/Fn2/Conservative.lean:33-43 @dddc32d34]
[fn: fn2/meta/Fn2/Conservative.lean:80-122 @dddc32d34]

The witness `revision_counts` adds annotations while retaining the base
post-count property. The broken revision also increments the post count on
annotation. `badRevision_breaks_counts` shows the property failing, and
`badRevision_annotate_not_square` shows the missing certificate premise.
These remain two theorems, not one packaged hypothesis-removal statement.
[fn: fn2/meta/Fn2/Conservative.lean:199-220 @dddc32d34]

Parametricity also requires an explicit restriction. `Client` can issue
commands, observe through the interface and return a result; it has no
representation-reading operation. `Related` supplies related initial states,
command preservation and equal observations. `abstraction` proves equal
client results under those premises.
[fn: fn2/meta/Fn2/Param.lean:28-64 @dddc32d34]

`counter_doubled_clients` is the positive witness. A raw-reading client breaks
the abstraction in `peek_breaks_abstraction`; removing command preservation
while retaining initial-state and observation agreement breaks it in
`drop_exec_breaks`. An ACL2 client needs an established interface restriction
and the primitive correspondence, not a registry label saying "abstract."
[fn: fn2/meta/Fn2/Param.lean:73-138 @dddc32d34]

The project's top semantic statements have satisfiable witnesses and teeth;
this is not a claim that every helper lemma has an independent audit.
Structural laws, registry evaluations and the conditional Q1 specialization
have the distinct roles recorded in the statement inventory.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:61-75 @worktree, read 2026-10-29]

## 6.6 The tenth artifact is generated presentation data

Hand-copying declarations into Lean creates a second specification that can
continue building after the ACL2 declaration changes. The tenth-artifact rule
makes the Lean presentation an output of the declaration infrastructure.
`Artifact` lists it beside the carrier, accessors, codec, logical view,
registry row, obligations, simulator hooks, owed stubs and lowering.
[fn: fn2/meta/Fn2/Decl.lean:52-57 @dddc32d34]

The implemented path is:

```text
ACL2 world tables
  -> print-registry.lsp
  -> registry.sexp
  -> emit_lean.py
  -> Fn2/Instances/LayerA.lean
```

[fn: fn2/meta/emit/print-registry.lsp:7-25 @dddc32d34]
[fn: fn2/meta/emit/emit.sh:12-16 @dddc32d34]

The printer includes the reference book, reads the machine, columns,
core-child and owed tables, and also prints the core-instance seal.
The emitter constructs its registry from the four declaration families.
[fn: fn2/meta/emit/print-registry.lsp:14-22 @dddc32d34]
[fn: fn2/meta/emit/emit_lean.py:292-308 @dddc32d34]

In the pinned export, `declaration_counts` checks 43 declarations:
3 machines, 9 columns tables, 9 core children and 22 owed rows.
`q1_case_counts` checks 31 machine-owned cases and 39 cases in the combined
catalogue. These are regression facts about this export, not proof totals.
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:30-49 @dddc32d34]

The other eight cases are explicitly hand-declared in `nonRegistryCases`:
the router fallback and seven executor cases. They sit in the handwritten
facts file, outside generated `LayerA.lean`, and are flagged until their case
source is registered in the world. Counting them as emitted would be wrong.
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:35-44 @dddc32d34]

The emitter checks row keys against consumed and explicitly omitted keys.
Unknown or missing consumed keys stop emission. Capacities, initializers and
formulas become `Opaque` text; a formula is never translated into a Lean
proposition by this exporter.
[fn: fn2/meta/emit/emit_lean.py:124-128 @dddc32d34]
[fn: fn2/meta/emit/emit_lean.py:205-234 @dddc32d34]
[fn: fn2/meta/emit/emit_lean.py:271-282 @dddc32d34]

Consequently, `registry_wf` checks recorded-row and cross-row consistency.
It cannot check omitted behavior or interpret opaque initializers.
Even the machine-row predicate expressly omits symbol classes, initial-value
syntax, the first column's name and presence of the common columns.
[fn: fn2/meta/Fn2/Decl.lean:159-188 @dddc32d34]
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:22-23 @dddc32d34]

## 6.7 A licence is an implication, not an import

The Q1 catalogue does not contain Q1 proofs. `q1Squares` constructs schema,
owner and case records; `q1_licensed` still takes the per-case simulation
squares as a hypothesis.
[fn: fn2/meta/Fn2/Decl.lean:219-230 @dddc32d34]
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:51-64 @dddc32d34]

Its content, in ASCII notation, is:

```text
Given:
  for every c in q1Cases,
    Sq R (stepA c) (run stepB (h c)) R

Conclude:
  for every word w whose labels belong to q1Cases,
    Sq R (run stepA w) (run stepB (expand h w)) R
```

[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:60-64 @dddc32d34]

ACL2 must establish the concrete instance properties. For fn2's proposed Q1
decomposition, the intermediate relation normalizes reference work counters:
the concrete loop accounts after each transition, while the reference carries
counters in arguments until exit. Raw core equality would state the wrong
intermediate contract.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:252-261 @worktree, read 2026-10-29]

Entry, exit, termination, selector coverage and accounting remain separate
ACL2 obligations. The exported `FN2-TURN-REFINEMENT` row still records equal
status and counts, well-formed resulting cores, the representation relation
and action/work bounds. A composition licence cannot erase those conclusions.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:277 @worktree, read 2026-10-29]
[fn: fn2/docs/OWED.md:33 @127f7b877]

Keep the source formula and the translated formula. Bind an admitted theorem
by its actual formula, accounting for the owed wrapper, rather than by a
matching name. fn2 has not completed that bridge here: `defthm-owed` stores
the untranslated formula even though its generated definition is translated.
[fn: fn2/books/owed.lisp:11-20 @127f7b877]
[fn: build/coordinator/fn2/DSL-METATHEORY.md:513 @worktree, read 2026-10-29]

No ACL2 proof object enters Lean in this arrangement, and no Lean axiom is
generated from a status row. If an ACL2 premise has only finite check evidence,
the row stays owed. Composition applies only to the covered trajectories whose
intermediate states and contracts actually join, not to unrelated runs sharing
seed numbers.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:142-146 @worktree, read 2026-10-29]

## 6.8 The bridge adds one assumption with six clauses

A name-preserving export can still attach the wrong meaning to the right name.
The bridge assumption concerns both the exported presentation and its supplied
interpretation: each used declaration, case and obligation identifies its
ACL2 subject, and each Lean premise means the recorded ACL2 property with the
same domains, boundaries, outputs, effects and observation contract.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:154-158 @worktree, read 2026-10-29]

The assumption has six separately inspectable clauses:

| Clause | Required correspondence |
|---|---|
| Identity | Qualified names designate the same declarations, functions and events |
| Payload | Values and order survive; unsupported payloads are explicit |
| Artifact | Exported subjects are the artifacts actually admitted, including assembly outputs |
| Obligation | A catalogue case binds the intended statement; catalogue existence does not imply coverage |
| Semantic | The interpreted Lean premise expresses the ACL2 formula's property |
| Evidence | Proof and check records concern that subject at that revision |

[fn: build/coordinator/fn2/LEAN-METATHEORY.md:158 @worktree, read 2026-10-29]

"One new assumption" means one bridge assumption. It does not replace trust
in either prover's kernel, the execution environment or native execution.
Nor does carrying an opaque formula discharge the semantic clause.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:158-179 @worktree, read 2026-10-29]

On the ACL2 side, retain owner and case identity, contract and boundary,
endpoint names, formals and calling convention, source and translated formula,
proof reference, check scope and dependencies. A proof with an additional
unestablished hypothesis does not realize the advertised premise.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:144 @worktree, read 2026-10-29]

The documented pessimistic estimate is **7 engineer-days for exact
translated-statement binding and generated-artifact provenance**, inside or
beside the declaration and obligation-store work. It is an estimate for that
bridge work, not a measured implementation time.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:217 @worktree, read 2026-10-29]

## 6.9 Three mutation controls, and the measured limit

A changed export and a rejected export answer different questions.
The first shows that some payload was captured; the second shows that a named
asserted property noticed the change. fn2's three controls separate these
outcomes from a change that the exporter cannot see at all.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:160-175 @worktree, read 2026-10-29]

**Row-only mutation.** `observes-row.sh` changes the recorded observations to
their tail, dropping each machine's first event. The saved diff removes the
three observation entries and changes machine-owned cases from 31 to 28.
That contradicts the pinned `q1_case_counts` assertion.
[fn: fn2/meta/emit/mutations/observes-row.sh:2-13 @dddc32d34]
[fn: fn2/meta/emit/mutations/observes-row.diff:8-12 @dddc32d34]
[fn: fn2/meta/emit/mutations/observes-row.diff:81-103 @dddc32d34]
[fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:46-49 @dddc32d34]

ACL2 rejects this mutant first, in the generated observation router's guard
proof. The coordinator records that the mutant world was then readable without
proofs. Its emitted data is diagnostic evidence, not a certified mutant instance.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:164-165 @worktree, read 2026-10-29]

**Field-width mutation.** `deadline-width.sh` narrows the common deadline
from `:u60` to `:u32`. The saved diff changes all six carrying rows: each
machine and its columns declaration. ACL2 certifies the mutant, and no pinned
Lean control fails; the changed payload is the evidence.
[fn: fn2/meta/emit/mutations/deadline-width.sh:7-18 @dddc32d34]
[fn: fn2/meta/emit/mutations/deadline-width.diff:3-56 @dddc32d34]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:167 @worktree, read 2026-10-29]

**Behavior-only mutation: the measured limit.** `retired-behaviour.sh` removes
the retired-phase exclusion from the generated `NAME-OBSERVES-P` predicate.
At the chapter's ACL2 pin, that exclusion is at line 231; the separate table
row begins at line 235 and contains no body binding.
[fn: fn2/meta/emit/mutations/retired-behaviour.sh:2-12 @dddc32d34]
[fn: fn2/books/machines.lisp:228-241 @127f7b877]

The recorded result is exact: ACL2 certified the mutant, the printed registry
was byte-identical and the emitted model had a zero-line diff. This refutes
artifact fidelity for the table-only exporter. It does not refute Lean's
theorems about the unchanged presentation.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:171-175 @worktree, read 2026-10-29]

The remedy is a `:generated` manifest binding emitted names to admitted bodies,
exported as opaque text with fingerprints. Record producer and emitting
section as well as signatures; assembly-generated functions cannot be
identified reliably by the declaration book's filename.
[fn: build/coordinator/fn2/DSL-METATHEORY.md:145-158 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/DSL-METATHEORY.md:504 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:173-175 @worktree, read 2026-10-29]

A fingerprint exposes a changed captured body; it does not interpret that body
or prove its correctness. `examples/assured/registry-emit.lisp` reproduces
both halves in one book. Its declaration macro `defkind` records a row and
generates `NAME-OBSERVES-P`, which must refuse events in the `:retired`
phase; `defkind-mutant` is the same generator with the exclusion removed,
writing the same row. Declared once with each, the table-only exports are
equal (`export-row`), the behaviours differ (the mutant observes a
`:send-result` while retired), and the manifest export, which adds each
generated function's admitted body as the world stores it
(`export-row-with-bodies`), differs. One world cannot hold two versions of
one macro, which is why the book defines the mutated generator beside the
real one rather than editing it.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:158 @worktree, read 2026-10-29]
[example: examples/assured/registry-emit.lisp]

## 6.10 A reading is not a build

The review missed concrete failures. Astra's sessions 2 and 3 collectively read
every Lean line and reviewed the additions, but predicted none of the three
errors found by the first `lake build`. The coordinator's conclusion is exact:
"a reading is not a build."
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:200-205 @worktree, read 2026-10-29]

The recorded failures and repairs were:

| Failure | Repair |
|---|---|
| Instance search could not see through `counter`'s carrier, reported as `HMul Nat counter.sigma doubled.sigma` (the Greek sigma spelled out) | Make the concrete implementations abbreviations |
| `omega` ignored hypotheses typed over the concealed carrier | Give the relevant binders explicit `Nat` types |
| Simplification unfolded the accept/close step before using its step hypothesis | Rewrite with that hypothesis first, then close by reflexivity |

[fn: build/coordinator/fn2/LEAN-METATHEORY.md:200-203 @worktree, read 2026-10-29]

The pinned code contains those repairs in the counter example and the identity
correspondence. Review improved the statements and witnesses, but it did not
substitute for elaboration.
[fn: fn2/meta/Fn2/Param.lean:73-94 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:451-466 @dddc32d34]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:226-227 @worktree, read 2026-10-29]

The recorded successful build used Lean 4.30.0 on the Mac. Its axiom census
covered 62 theorems, with dependencies confined to `propext`, `Quot.sound`
and `Classical.choice`, and none on `sorryAx`. The census source enumerates
the declarations; the coordinator records the execution result.
[fn: fn2/meta/AxiomCensus.lean:1-65 @dddc32d34]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:9 @worktree, read 2026-10-29]

For this project the recorded commands are `lake build` in `fn2/meta` and
`lake env lean AxiomCensus.lean`. Keep the build result, axiom census,
export freshness and instance bindings separate: each answers a different
question about what is assured.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:193-198 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:215 @worktree, read 2026-10-29]

## 6.11 Information, not a gate

A policy of treating metatheory as information does not permit calling a failed
proof proved. The fn2 decision is that Lean is not a shipping prerequisite
before the first release; a failed Lean check still withdraws the corresponding
proof claim. An admitted theorem, translated owed row and passing check remain
different kinds of assurance.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:215 @worktree, read 2026-10-29]

This arrangement cannot establish ACL2's soundness, the truth of an opaque
formula, universal validity from bounded checks, or durability, fairness and
environmental integrity from simulation squares. A theorem name in a row
does not establish that the theorem has the advertised statement.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:177-179 @worktree, read 2026-10-29]

It also does not establish frame completeness: that every intended pair of
interchangeable routes is connected by the generated diagrams. The implemented
coherence theorem concerns routes already connected by declared swaps.
The broader schema distinguishes diagram soundness from that completeness
conjecture, and distinguishes refinement into nondeterminism from equality.
[fn: fn2/meta/Fn2/Coherence.lean:111-119 @dddc32d34]
[fn: build/coordinator/fn2/COHERENCE.md:291-303 @worktree, read 2026-10-29]

The ACL2 work remains concrete: generate and record declarations, bind every
obligation to its translated formula, fingerprint admitted generated bodies,
prove the named-function instances, and retain finite checks as finite evidence.
The metatheory explains how those premises compose; the registry must never
pretend to have supplied them.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:142-158 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:217 @worktree, read 2026-10-29]
