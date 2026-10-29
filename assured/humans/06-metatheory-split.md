# 6. The metatheory split: Lean for frame theorems, ACL2 for instances

Use ACL2 to prove properties of the implementation's named functions. Use
Lean to prove **frame theorems**: general implications saying how local
properties compose. The **bridge** must identify which ACL2 statements and
generated artifacts supply the premises of those Lean implications. This is
the engineering split used by fn2. [^s1]

For example, a frame theorem can say that a square for each transition case
gives a square for a whole run. ACL2 must still prove the concrete
transition cases, and the bridge must bind them to the cases Lean means. The
following failure shows why that binding matters. [^s2]

A green Lean build can describe yesterday's registry while today's generated
behavior has changed. In fn2's mutation experiment, removing the
retired-phase exclusion from an observation predicate left the printed
registry byte-identical. The emitted Lean model therefore stayed unchanged.
This is the first boundary to understand: reading declaration tables does
not establish fidelity to generated function bodies. [^s3]

A second boundary is logical: a theorem saying that local squares compose
does not supply those squares. A third is evidential: a translated ACL2
statement, a passing executable check, an admitted ACL2 theorem and a Lean
theorem retain different statuses. No proof-status row becomes an axiom on
the other side. [^s4]

This chapter reads the ACL2 books at `127f7b877` and the Lean project at
`dddc32d34`. The generated `LayerA.lean` in that Lean revision labels its
source `origin/fn2/main 137695dfc`; its counts and the recorded mutation
experiment belong to that export, not to a newly generated export of
`127f7b877`. [^s5] [^s6]

## 6.1 Classify the obligation by its subject

Moving a difficult ACL2 theorem to Lean because it quantifies over every
execution changes the engineering boundary for the wrong reason. A theorem
about a named machine's executions remains an instance theorem; its code,
guards, representation relation and arithmetic live in the ACL2 world. [^s7]

The working decision rule has four cases: [^s1]

| Subject | Home | What must be supplied |
|---|---|---|
| Named functions, a concrete representation, a converter or an admitted book | ACL2 | The actual instance statement, including outputs, effects, guards and bounds |
| Declaration presentations, interpretations or diagrams constructed from squares | Lean | A frame theorem parameterized by the instance properties |
| Correspondence between an exported row and its admitted ACL2 subject | The bridge | Identity, statement and artifact fidelity |
| Physical execution, environmental evidence or eventual progress | The relevant execution model and evidence | Explicit adapter, persistence and fairness premises |

This is an engineering division, not a claim that first-order logic cannot
express metatheory. ACL2 could encode presentations and diagrams as data.
The cost would include maintaining that encoding, its induction principles
and the categorical vocabulary. The fn2 decision puts that frame in Lean
with Mathlib and keeps named-function proofs beside the ACL2 implementation.
[^s8]

For an ACL2 user, the practical question is therefore precise: does this
obligation concern the functions in this world, or the construction that
combines arbitrary instances satisfying a stated interface? The first stays
in ACL2; the second can become a reusable Lean implication. [^s9]

## 6.2 Record declarations without manufacturing theorems

A registry becomes misleading when a row's existence is treated as evidence
that its advertised property holds. ACL2's manual gives the intended
boundary: "By convention, no user-defined table is important to ACL2's
soundness." Tables store user data in the world; they are not a second
theorem-admission mechanism. [^s10]

Record the declaration where the macro generates its artifacts. In fn2,
`fn2-machine-events` emits both `defcolumns` and the machine's functions,
then writes `fn2-machine-kinds`. The row records states, columns,
continuations, observed events and other declaration data. It does not
record admitted bodies. [^s11]

Use a qualified identity. The same declaration emits a machine and a columns
table with the same bare name; identifying both by name alone conflates
them. The Lean fact `ids_qualified` checks that qualified identities are
unique while the bare names are not. [^s12] [^s13]

An owed statement needs a different treatment from a proved statement. The
actual `defthm-owed` macro defines a `$OWED` function with `defun-nx` and
records the source formula, variables, teeth and `:owed` status. It admits
no theorem asserting that formula. [^s14]

The manual calls `defun-nx` a way to "Define a non-executable function
symbol"; it says the resulting calls "cannot be evaluated." The evaluating
teeth are therefore separate functions. fn2 resolves each named tooth,
requires zero arguments and emits an assertion that its result equals `t`.
[^s15] [^s16]

For the executable check, the manual describes `assert-event` as checking
that evaluation returns "a non-`nil` value, causing an error otherwise."
fn2's `(equal (tooth) t)` form makes the required tooth result exact. That
check remains evidence; the exported obligation remains owed. [^s17] [^s18]

`examples/assured/owed.lisp` keeps the distinction in a world table: its
`defthm-owed` admits a `defun-nx` of the statement (so a statement naming an
undefined function is refused at once, as the book shows), runs each named
tooth and requires exactly `t`, and records the row as `:owed`; its
`defthm-claimed` is `defthm` plus a `:proved` row; `claim-counts` reads the
table, and the book asserts `(1 1)`. Teeth given as prose are refused
[^s19].

## 6.3 Compose simulation squares in two directions

`Sq` is the local simulation claim: from related states, a successful source
transition has a successful target transition ending in related states. The
double-category structure organizes how such claims compose; each use still
requires a proof of its square. [^s20]

A **double category** has two directions of arrows and squares between them.
Here the objects are state types. One direction describes execution: partial
transitions, called **loose arrows**. The other describes changes of
representation: state relations, called **tight arrows**. A partial
transition returns an optional next state; absence means the transition is
not enabled. The tight arrows connect to Mathlib's `RelCat`, and
`Tight.toRelCat_comp` identifies their composition with relational
composition. [^s21]

`Sq.seq` composes squares along transitions; `Sq.stack` composes them along
representation relations. `Sq.idLoose` and `Sq.idTight` supply the
identities. The squares are propositions. `Sq.thin` uses proof irrelevance:
any two proofs of the same proposition are equal. `Sq.interchange` then says
that composing a grid along one direction and then the other gives the same
proof of its outside square. It does not compare data transported by
different routes. [^s22]

Do not strengthen that description to a framed double category. fn2's
earlier interpretation of `restrict` as a cartesian lift was wrong. The
implemented operation is a weakest precondition on an input pair; its
documentation explicitly withdraws the framing claim for partial
transitions. [^s23]

The useful composition theorem is `Sq.paste`: a square for every label gives
a square for every word, allowing a source label to mean a finite target
word. `Sq.paste_cover` adds a catalogue restriction: every label in the run
must belong to the catalogue whose cases have squares. [^s24]

Dropping that coverage premise is unsound. `uncovered_catalogue_holds`
proves the square for the catalogue containing `false`;
`uncovered_case_fails` gives a run using `true` for which the square fails.
Enumerating the cases you know does not prove that every executed case is
among them. [^s25]

## 6.4 Coherence needs both a witness and a broken sibling

"Different machines" is not an independence theorem. In the accept/close
toy, the listener and an echo connection share the allocator's free count.
With no free row and one outstanding close, accept-then-close admits zero
connections; close-then-accept admits one. [^s26] [^s27]

The theorem `coherence` has a narrower and useful statement. Given a
correspondence containing the G1 step squares and observation agreement,
implementation diamonds, a G0-related start, trace-equivalent words and a
successful implementation run, it supplies a successful reference run with
equal observations. It does not assert that arbitrary schedules complete.
[^s28]

Here `TraceEq` is generated by adjacent swaps of declared-independent
labels. `Diamonds` requires equal two-step partial runs for each declared
pair. It does not alone establish preservation of enabledness: two actions
that disable one another can have equal failing composite runs. [^s29]

`IndependentDiamonds` includes enabledness preservation. The footprint
theorems establish both properties when each action respects its declared
reads and writes and neither writes what the other reads or writes.
Declaring empty footprints while writing anyway is exposed by `liar_indep`,
`liar_not_respects` and `liar_not_diamond`. [^s30] [^s31]

The positive coherence witness is `twoRecv_coherence_witness`: two receive
counters start at zero, the orders are trace-equivalent, both executions
succeed and their observation agrees with a reference total of two. The G1
squares and observation edge are fields of `sumCorr`. [^s32]

The tooth `acceptClose_without_g2` packages every other coherence premise
with failure of the conclusion. Its identity correspondence retains G1 and
observation agreement; the false independence declaration loses G2. This is
the shape to demand of a hypothesis-removal test on the ACL2 side: retain
the other premises and exhibit the failed conclusion. [^s33]

## 6.5 Preserve old behavior and hide representation details

The next two results cover different forms of change. **Behavioral
conservativity** relates the runs of a revised system to those of its base
system. **Parametricity** shows that a client restricted to an interface
gets the same results from implementations related through that interface.
[^s34] [^s35]

A theorem named `conservative` can invite a larger claim than its statement
supports. This one concerns behavior of runs. It does not represent a syntax
of theories, a derivability relation or a model-expansion theorem. [^s36]

Its `Extension` certificate supplies a projection, label translation,
converter, a square per revised label and lifting of base events. Under that
certificate, `runs_exactly` identifies base runs with projected and
translated revised runs; `conservative` transports every property of a base
word and its final state. [^s37] [^s34]

The witness `revision_counts` adds annotations while retaining the base
post-count property. The broken revision also increments the post count on
annotation. `badRevision_breaks_counts` shows the property failing, and
`badRevision_annotate_not_square` shows the missing certificate premise.
These remain two theorems, not one packaged hypothesis-removal statement.
[^s38]

Parametricity also requires an explicit restriction. `Client` can issue
commands, observe through the interface and return a result; it has no
representation-reading operation. `Related` supplies related initial states,
command preservation and equal observations. `abstraction` proves equal
client results under those premises. [^s35]

`counter_doubled_clients` is the positive witness. A raw-reading client
breaks the abstraction in `peek_breaks_abstraction`; removing command
preservation while retaining initial-state and observation agreement breaks
it in `drop_exec_breaks`. An ACL2 client needs an established interface
restriction and the primitive correspondence, not a registry label saying
"abstract." [^s39]

The project's top semantic statements have satisfiable witnesses and teeth;
this is not a claim that every helper lemma has an independent audit.
Structural laws, registry evaluations and the conditional Q1 specialization
have the distinct roles recorded in the statement inventory. [^s40]

## 6.6 Generate the Lean presentation from ACL2 declarations

Hand-copying declarations into Lean creates a second specification that can
continue building after the ACL2 declaration changes. fn2 therefore treats
the Lean presentation as a tenth generated artifact of a declaration.
`Artifact` lists it beside the carrier, accessors, codec, logical view,
registry row, obligations, simulator hooks, owed stubs and lowering. [^s41]

The implemented path is: [^s42] [^s43]

```text
ACL2 world tables
  -> print-registry.lsp
  -> registry.sexp
  -> emit_lean.py
  -> Fn2/Instances/LayerA.lean
```

The printer includes the reference book, reads the machine, columns,
core-child and owed tables, and also prints the core-instance seal. The
emitter constructs its registry from the four declaration families.
[^s44] [^s45]

In the pinned export, `declaration_counts` checks 43 declarations: 3
machines, 9 columns tables, 9 core children and 22 owed rows.
`q1_case_counts` checks 31 machine-owned cases and 39 cases in the combined
catalogue. These are regression facts about this export, not proof totals.
[^s46]

The other eight cases are explicitly hand-declared in `nonRegistryCases`:
the router fallback and seven executor cases. They sit in the handwritten
facts file, outside generated `LayerA.lean`, and are flagged until their
case source is registered in the world. Counting them as emitted would be
wrong. [^s47]

The emitter checks row keys against consumed and explicitly omitted keys.
Unknown or missing consumed keys stop emission. Capacities, initializers and
formulas become `Opaque` text; a formula is never translated into a Lean
proposition by this exporter. [^s48] [^s49] [^s50]

Consequently, `registry_wf` checks the consistency of recorded rows, both
individually and with one another. Initializers and other omitted behavior
remain outside its semantic interpretation. Even the machine-row predicate
expressly omits symbol classes, initial-value syntax, the first column's
name and presence of the common columns. [^s51] [^s52]

## 6.7 Supply the instance premises of the composition theorem

The Q1 catalogue does not contain Q1 proofs. `q1Squares` constructs schema,
owner and case records; `q1_licensed` still takes the per-case simulation
squares as a hypothesis. [^s53] [^s2]

Its content, in ASCII notation, is: [^s54]

```text
Given:
  for every c in q1Cases,
    Sq R (stepA c) (run stepB (h c)) R

Conclude:
  for every word w whose labels belong to q1Cases,
    Sq R (run stepA w) (run stepB (expand h w)) R
```

ACL2 must establish the concrete instance properties. For fn2's proposed Q1
decomposition, the intermediate relation normalizes reference work counters:
the concrete loop accounts after each transition, while the reference
carries counters in arguments until exit. Raw core equality would state the
wrong intermediate contract. [^s55]

Entry, exit, termination, selector coverage and accounting remain separate
ACL2 obligations. The exported `FN2-TURN-REFINEMENT` row still records equal
status and counts, well-formed resulting cores, the representation relation
and action/work bounds. A composition licence cannot erase those
conclusions. [^s56] [^s57]

Keep the source formula and the translated formula. Bind an admitted theorem
by its actual formula, accounting for the owed wrapper, rather than by a
matching name. fn2 has not completed that bridge here: `defthm-owed` stores
the untranslated formula even though its generated definition is translated.
[^s58] [^s59]

No ACL2 proof object enters Lean in this arrangement, and no Lean axiom is
generated from a status row. If an ACL2 premise has only finite check
evidence, the row stays owed. Composition applies only to the covered
trajectories whose intermediate states and contracts actually join, not to
unrelated runs sharing seed numbers. [^s60]

## 6.8 The bridge adds one assumption with six clauses

A name-preserving export can still attach the wrong meaning to the right
name. The bridge assumption concerns both the exported presentation and its
supplied interpretation: each used declaration, case and obligation
identifies its ACL2 subject, and each Lean premise means the recorded ACL2
property with the same domains, boundaries, outputs, effects and observation
contract. [^s61]

The assumption has six separately inspectable clauses: [^s62]

| Clause | Required correspondence |
|---|---|
| Identity | Qualified names designate the same declarations, functions and events |
| Payload | Values and order survive; unsupported payloads are explicit |
| Artifact | Exported subjects are the artifacts actually admitted, including assembly outputs |
| Obligation | A catalogue case binds the intended statement; catalogue existence does not imply coverage |
| Semantic | The interpreted Lean premise expresses the ACL2 formula's property |
| Evidence | Proof and check records concern that subject at that revision |

"One new assumption" means one bridge assumption. It does not replace trust
in either prover's kernel, the execution environment or native execution.
Nor does carrying an opaque formula discharge the semantic clause. [^s63]

On the ACL2 side, retain owner and case identity, contract and boundary,
endpoint names, formals and calling convention, source and translated
formula, proof reference, check scope and dependencies. A proof with an
additional unestablished hypothesis does not realize the advertised premise.
[^s64]

The documented pessimistic estimate is **7 engineer-days for exact
translated-statement binding and generated-artifact provenance**, inside or
beside the declaration and obligation-store work. It is an estimate for that
bridge work, not a measured implementation time. [^s65]

## 6.9 Three mutation controls, and the measured limit

A changed export and a rejected export answer different questions. The first
shows that some payload was captured; the second shows that a named asserted
property noticed the change. fn2's three controls separate these outcomes
from a change that the exporter cannot see at all. [^s66]

**Row-only mutation.** `observes-row.sh` changes the recorded observations
to their tail, dropping each machine's first event. The saved diff removes
the three observation entries and changes machine-owned cases from 31 to 28.
That contradicts the pinned `q1_case_counts` assertion. [^s67] [^s68]
[^s69] [^s70]

ACL2 rejects this mutant first, in the generated observation router's guard
proof. The coordinator records that the mutant world was then readable
without proofs. Its emitted data is diagnostic evidence, not a certified
mutant instance. [^s71]

**Field-width mutation.** `deadline-width.sh` narrows the common deadline
from `:u60` to `:u32`. The saved diff changes all six carrying rows: each
machine and its columns declaration. ACL2 certifies the mutant, and no
pinned Lean control fails; the changed payload is the evidence. [^s72] [^s73]
[^s74]

**Behavior-only mutation: the measured limit.** `retired-behaviour.sh`
removes the retired-phase exclusion from the generated `NAME-OBSERVES-P`
predicate. At the chapter's ACL2 pin, that exclusion is at line 231; the
separate table row begins at line 235 and contains no body binding.
[^s75] [^s76]

The recorded result is exact: ACL2 certified the mutant, the printed
registry was byte-identical and the emitted model had a zero-line diff. This
refutes artifact fidelity for the table-only exporter. It does not refute
Lean's theorems about the unchanged presentation. [^s77]

The remedy is a `:generated` manifest binding emitted names to admitted
bodies, exported as opaque text with fingerprints. Record producer and
emitting section as well as signatures; assembly-generated functions cannot
be identified reliably by the declaration book's filename. [^s78] [^s79]
[^s80]

A fingerprint exposes a change in a captured body. Establishing that the new
body is correct remains a separate proof obligation. [^s62]

`examples/assured/registry-emit.lisp` demonstrates the distinction:

1. `defkind` records a declaration row and generates `NAME-OBSERVES-P`,
   which refuses events in the `:retired` phase.
2. `defkind-mutant` records the same row but omits that refusal. The book
   defines both generators so it can compare them in one ACL2 world.
3. `export-row` gives equal table-only exports, although the mutant
   accepts `:send-result` while retired.
4. `export-row-with-bodies` includes each generated function's admitted
   body as stored in the world. These exports differ.

The example detects the body change; it does not interpret the body or prove
the new implementation correct. [^s81]

### A later declaration experiment: E2 pass 3

The later E2 experiment tested one public `defsquare` form with two
consumers: Q1 executor/reference correspondence and Q4 read-state
history/summary correspondence. Its result supports **a common declaration
form with specialized statement templates**. Both consumers generate
statements from declared semantic roles, such as the relation, steps and
observations. They do not share one universal semantic template. [^s82]

The common code requires every function named by an effective role to occur
in the translated statement, unless that row explicitly names the role as
unused. It rejects missing, duplicate or redundant exceptions. This detects
a declared relation that is absent from the statement; it does not prove
that a function has the right meaning or occurs in the right argument
position. Exact proof-formula matching and semantic negative controls remain
necessary. [^s83]

The recorded result has 45 correspondence rows: 40 owed Q1 statements and
five proved Q4 statements, with 83 separate evidence records. Fresh ORIGINAL
campaigns completed 10,004 G1 checks across 19 of 39 cases; 20 cases
remained unexercised. All 14 books passed local `certify-book` in under 60
seconds each. These counts describe E2's own package, not a refreshed proof
status for the earlier layer-A ledger. [^s82]

The package cost 2,085 physical source lines: 1,454 new and 631 copied.
Fourteen lines were wrapped consumer declarations; the remaining 2,071 were
support. There was no implemented manual-registration baseline, so this
measures the cost of the common form, not net source savings. The wrappers,
specialized builders, unused-role exceptions, proof bridges and checker
adapters are part of that cost. [^s84]

E2 thus answers a narrower question than the Lean bridge experiment: a
shared form can generate and bind useful statements for two consumers. Q1's
checks can still miss a shared-handler defect that the client oracle
catches; Q4 proves its chosen relation and observations, not their
conformance to an external protocol. [^s85]

## 6.10 A reading is not a build

The review missed concrete failures. Astra's sessions 2 and 3 collectively
read every Lean line and reviewed the additions, but predicted none of the
three errors found by the first `lake build`. The coordinator's conclusion
is exact: "a reading is not a build." [^s86]

The recorded failures and repairs were: [^s87]

| Failure | Repair |
|---|---|
| Instance search could not see through `counter`'s carrier, reported as `HMul Nat counter.sigma doubled.sigma` (the Greek sigma spelled out) | Make the concrete implementations abbreviations |
| `omega` ignored hypotheses typed over the concealed carrier | Give the relevant binders explicit `Nat` types |
| Simplification unfolded the accept/close step before using its step hypothesis | Rewrite with that hypothesis first, then close by reflexivity |

The pinned code contains those repairs in the counter example and the
identity correspondence. Review improved the statements and witnesses, but
it did not substitute for elaboration. [^s88] [^s89] [^s90]

The recorded successful build used Lean 4.30.0 on the Mac. Its axiom census
covered 62 theorems, with dependencies confined to `propext`, `Quot.sound`
and `Classical.choice`, and none on `sorryAx`. The census source enumerates
the declarations; the coordinator records the execution result. [^s91] [^s92]

For this project the recorded commands are `lake build` in `fn2/meta` and
`lake env lean AxiomCensus.lean`. Keep the build result, axiom census,
export freshness and instance bindings separate: each answers a different
question about what is assured. [^s93] [^s94]

## 6.11 Information, not a gate

A policy of treating metatheory as information does not permit calling a
failed proof proved. The fn2 decision is that Lean is not a shipping
prerequisite before the first release; a failed Lean check still withdraws
the corresponding proof claim. An admitted theorem, translated owed row and
passing check remain different kinds of assurance. [^s94]

This arrangement cannot establish ACL2's soundness, the truth of an opaque
formula, universal validity from bounded checks, or durability, fairness and
environmental integrity from simulation squares. A theorem name in a row
does not establish that the theorem has the advertised statement. [^s95]

It also does not establish frame completeness: that every intended pair of
interchangeable routes is connected by the generated diagrams. The
implemented coherence theorem concerns routes already connected by declared
swaps. The broader schema distinguishes diagram soundness from that
completeness conjecture, and distinguishes refinement into nondeterminism
from equality. [^s96] [^s97]

The ACL2 work remains concrete: generate and record declarations, bind every
obligation to its translated formula, fingerprint admitted generated bodies,
prove the named-function instances, and retain finite checks as finite
evidence. The metatheory explains how those premises compose; the registry
must never pretend to have supplied them. [^s98] [^s65]

[Part 3 contents](../README.md) | [Previous chapter](05-transport.md) | [Next chapter](07-honest-costs.md)

[^s1]: [fn: fn2/docs/design/LEAN-METATHEORY.md:44-57 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L44).

[^s2]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:51-64 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L51).

[^s3]: [fn: fn2/docs/design/LEAN-METATHEORY.md:169-175 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L169).

[^s4]: [fn: fn2/docs/design/LEAN-METATHEORY.md:128-148 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L128).

[^s5]: [fn: fn2/meta/Fn2/Instances/LayerA.lean:1-6 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerA.lean#L1).

[^s6]: [fn: fn2/meta/Fn2/Instances/LayerA.lean:771 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerA.lean#L771).

[^s7]: [fn: fn2/docs/design/LEAN-METATHEORY.md:44-49 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L44).

[^s8]: [fn: fn2/docs/design/LEAN-METATHEORY.md:25 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L25).

[^s9]: [fn: fn2/docs/design/LEAN-METATHEORY.md:46-48 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L46).

[^s10]: [:doc table]

[^s11]: [fn: fn2/books/machines.lisp:203-241 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L203).

[^s12]: [fn: fn2/books/machines.lisp:213 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L213).

[^s13]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:25-28 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L25).

[^s14]: [fn: fn2/books/owed.lisp:11-22 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/owed.lisp#L11).

[^s15]: [:doc defun-nx]

[^s16]: [fn: fn2/books/owed.lisp:29-49 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/owed.lisp#L29).

[^s17]: [:doc assert-event]

[^s18]: [fn: fn2/docs/OWED.md:3-8 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L3).

[^s19]: [example: examples/assured/owed.lisp] [Source](../../examples/assured/owed.lisp).

[^s20]: [fn: fn2/meta/Fn2/Square.lean:79-83 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L79).

[^s21]: [fn: fn2/meta/Fn2/Square.lean:29-75 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L29).

[^s22]: [fn: fn2/meta/Fn2/Square.lean:97-147 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L97).

[^s23]: [fn: fn2/meta/Fn2/Square.lean:85-95 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L85).

[^s24]: [fn: fn2/meta/Fn2/Square.lean:172-205 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L172).

[^s25]: [fn: fn2/meta/Fn2/Coherence.lean:489-510 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L489).

[^s26]: [fn: fn2/meta/Fn2/Coherence.lean:342-417 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L342).

[^s27]: [fn: fn2/meta/Fn2/Coherence.lean:438-447 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L438).

[^s28]: [fn: fn2/meta/Fn2/Coherence.lean:97-119 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L97).

[^s29]: [fn: fn2/meta/Fn2/Coherence.lean:59-82 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L59).

[^s30]: [fn: fn2/meta/Fn2/Coherence.lean:138-150 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L138).

[^s31]: [fn: fn2/meta/Fn2/Coherence.lean:190-235 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L190).

[^s32]: [fn: fn2/meta/Fn2/Coherence.lean:292-338 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L292).

[^s33]: [fn: fn2/meta/Fn2/Coherence.lean:449-487 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L449).

[^s34]: [fn: fn2/meta/Fn2/Conservative.lean:80-122 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Conservative.lean#L80).

[^s35]: [fn: fn2/meta/Fn2/Param.lean:28-64 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Param.lean#L28).

[^s36]: [fn: fn2/meta/Fn2/Conservative.lean:11-17 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Conservative.lean#L11).

[^s37]: [fn: fn2/meta/Fn2/Conservative.lean:33-43 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Conservative.lean#L33).

[^s38]: [fn: fn2/meta/Fn2/Conservative.lean:199-220 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Conservative.lean#L199).

[^s39]: [fn: fn2/meta/Fn2/Param.lean:73-138 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Param.lean#L73).

[^s40]: [fn: fn2/docs/design/LEAN-METATHEORY.md:61-75 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L61).

[^s41]: [fn: fn2/meta/Fn2/Decl.lean:52-57 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Decl.lean#L52).

[^s42]: [fn: fn2/meta/emit/print-registry.lsp:7-25 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/print-registry.lsp#L7).

[^s43]: [fn: fn2/meta/emit/emit.sh:12-16 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/emit.sh#L12).

[^s44]: [fn: fn2/meta/emit/print-registry.lsp:14-22 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/print-registry.lsp#L14).

[^s45]: [fn: fn2/meta/emit/emit_lean.py:292-308 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/emit_lean.py#L292).

[^s46]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:30-49 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L30).

[^s47]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:35-44 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L35).

[^s48]: [fn: fn2/meta/emit/emit_lean.py:124-128 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/emit_lean.py#L124).

[^s49]: [fn: fn2/meta/emit/emit_lean.py:205-234 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/emit_lean.py#L205).

[^s50]: [fn: fn2/meta/emit/emit_lean.py:271-282 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/emit_lean.py#L271).

[^s51]: [fn: fn2/meta/Fn2/Decl.lean:159-188 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Decl.lean#L159).

[^s52]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:22-23 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L22).

[^s53]: [fn: fn2/meta/Fn2/Decl.lean:219-230 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Decl.lean#L219).

[^s54]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:60-64 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L60).

[^s55]: [fn: fn2/docs/design/DSL-METATHEORY.md:252-261 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L252).

[^s56]: [fn: fn2/docs/design/DSL-METATHEORY.md:277 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L277).

[^s57]: [fn: fn2/docs/OWED.md:33 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/OWED.md#L33).

[^s58]: [fn: fn2/books/owed.lisp:11-20 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/owed.lisp#L11).

[^s59]: [fn: fn2/docs/design/DSL-METATHEORY.md:513 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L513).

[^s60]: [fn: fn2/docs/design/LEAN-METATHEORY.md:142-146 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L142).

[^s61]: [fn: fn2/docs/design/LEAN-METATHEORY.md:154-158 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L154).

[^s62]: [fn: fn2/docs/design/LEAN-METATHEORY.md:158 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L158).

[^s63]: [fn: fn2/docs/design/LEAN-METATHEORY.md:158-179 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L158).

[^s64]: [fn: fn2/docs/design/LEAN-METATHEORY.md:144 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L144).

[^s65]: [fn: fn2/docs/design/LEAN-METATHEORY.md:217 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L217).

[^s66]: [fn: fn2/docs/design/LEAN-METATHEORY.md:160-175 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L160).

[^s67]: [fn: fn2/meta/emit/mutations/observes-row.sh:2-13 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/observes-row.sh#L2).

[^s68]: [fn: fn2/meta/emit/mutations/observes-row.diff:8-12 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/observes-row.diff#L8).

[^s69]: [fn: fn2/meta/emit/mutations/observes-row.diff:81-103 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/observes-row.diff#L81).

[^s70]: [fn: fn2/meta/Fn2/Instances/LayerAFacts.lean:46-49 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Instances/LayerAFacts.lean#L46).

[^s71]: [fn: fn2/docs/design/LEAN-METATHEORY.md:164-165 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L164).

[^s72]: [fn: fn2/meta/emit/mutations/deadline-width.sh:7-18 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/deadline-width.sh#L7).

[^s73]: [fn: fn2/meta/emit/mutations/deadline-width.diff:3-56 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/deadline-width.diff#L3).

[^s74]: [fn: fn2/docs/design/LEAN-METATHEORY.md:167 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L167).

[^s75]: [fn: fn2/meta/emit/mutations/retired-behaviour.sh:2-12 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/emit/mutations/retired-behaviour.sh#L2).

[^s76]: [fn: fn2/books/machines.lisp:228-241 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines.lisp#L228).

[^s77]: [fn: fn2/docs/design/LEAN-METATHEORY.md:171-175 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L171).

[^s78]: [fn: fn2/docs/design/DSL-METATHEORY.md:145-158 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L145).

[^s79]: [fn: fn2/docs/design/DSL-METATHEORY.md:504 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L504).

[^s80]: [fn: fn2/docs/design/LEAN-METATHEORY.md:173-175 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L173).

[^s81]: [example: examples/assured/registry-emit.lisp] [Source](../../examples/assured/registry-emit.lisp).

[^s82]: [fn: fn2/experiments/squares/E2-RESULTS.md:1-28 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L1).

[^s83]: [fn: fn2/experiments/squares/E2-RESULTS.md:74-115 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L74).

[^s84]: [fn: fn2/experiments/squares/E2-RESULTS.md:151-168 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L151).

[^s85]: [fn: fn2/experiments/squares/E2-RESULTS.md:18-23 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E2-RESULTS.md#L18).

[^s86]: [fn: fn2/docs/design/LEAN-METATHEORY.md:200-205 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L200).

[^s87]: [fn: fn2/docs/design/LEAN-METATHEORY.md:200-203 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L200).

[^s88]: [fn: fn2/meta/Fn2/Param.lean:73-94 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Param.lean#L73).

[^s89]: [fn: fn2/meta/Fn2/Coherence.lean:451-466 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L451).

[^s90]: [fn: fn2/docs/design/LEAN-METATHEORY.md:226-227 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L226).

[^s91]: [fn: fn2/meta/AxiomCensus.lean:1-65 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/AxiomCensus.lean#L1).

[^s92]: [fn: fn2/docs/design/LEAN-METATHEORY.md:9 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L9).

[^s93]: [fn: fn2/docs/design/LEAN-METATHEORY.md:193-198 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L193).

[^s94]: [fn: fn2/docs/design/LEAN-METATHEORY.md:215 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L215).

[^s95]: [fn: fn2/docs/design/LEAN-METATHEORY.md:177-179 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L177).

[^s96]: [fn: fn2/meta/Fn2/Coherence.lean:111-119 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L111).

[^s97]: [fn: fn2/docs/design/COHERENCE.md:291-303 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L291).

[^s98]: [fn: fn2/docs/design/LEAN-METATHEORY.md:142-158 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L142).
