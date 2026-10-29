# 3. Commuting squares: what a change preserves

A commuting square states that two ways of carrying out a change agree under
a specified relation. For a representation change, the question is: if the
old and new states agree now, do corresponding steps keep them in agreement?
For a scheduling change, it is: can these two actions exchange places
without changing the promised observations? A **diamond** draws the two
orders from a common starting state. [^s1] [^s2]

The reusable argument is local: establish the relation at entry, prove the
required step cases, then compose them into a claim about a run. The choice
of relation determines what the result protects. [^s3]

Equal answers now can conceal different answers after the next input. In the
guide's read-state example, histories containing `(:read 1)` and `(:read 2)`
both report one read article. After `(:read 1)`, their counts differ. The
theorem `rs-count2-rel-not-step-closed` exhibits the failure: the proposed
relation preserves today's observation but cannot support tomorrow's
substitution. [^s4]

A commuting square makes that missing condition explicit. It names the
representations, the relation between them, the transitions that preserve
it, and the observations that relation protects. Its useful promise is
compositional: local preservation extends to executions under stated
premises. Environment fidelity, progress, and completeness of the chosen
generators remain separate claims. [^s1] [^s5]

## 3.1 Define the states, steps and observations

The relation must be preserved by every admitted step. Equal current
observations are a candidate relation; the read-state counterexample
shows why that candidate still needs a preservation proof. [^s4]

Write a square as `(A, B, R, T, obs, kappa)`. Here `A` and `B` are state
representations; `R` relates their states; and each label in `T` has an
interpretation on both sides. A **label** names a step; a **word** is a
finite sequence of labels. One source label may mean several target steps,
or no target step. `obs_A` and `obs_B` name the observations. The **loss
contract** `kappa` specifies which differences may be ignored; identity loss
permits none. [^s1] [^s6]

In the drawing, `h(t)` is the target word for source label `t`. The vertical
lines assert the relation `R`; they need not be conversion functions. The
conditions are:

```text
       a  -------- t_A -------->  a'
       |                         |
       R                         R
       |                         |
       b  ----- run_B(h(t)) --->  b'

step:  R(a,b) => R(t_A(a), run_B(h(t),b))
edge:  R(a,b) => obs_A(a) =_kappa obs_B(b)
base:  R(init_A, init_B)
```

The diagram abbreviates legal transitions on admissible states; the
partial-transition version supplies a matching target execution whenever the
source transition succeeds. [^s1] [^s7]

The three conditions do different work. **Step** supports continuation.
**Edge** connects the internal relation to the user's contract. **Base**
establishes the relation at initialization or conversion. A correct step
theorem cannot repair a converter that starts outside the relation. [^s8]

Outputs and refusals belong in the matching condition. If the observation is
an emitted history, retain that history in the semantic state or carry a
monitor that observes it. Agreement at the final state cannot recover a
reply that differed earlier, and a matching word cannot hide an externally
distinguishable action prefix or crash cut. [^s9] [^s10]

## 3.2 An inventory finds recurring obligations, not completed proofs

A table of squares can look like a table of guarantees even when its rows
are specifications, checked instances, or assumptions. The fn2 inventory
explicitly mixes those statuses. Its Q1-Q25 snapshot is evidence that the
shape recurs; it is not evidence that twenty-five correctness claims have
been proved. [^s11]

The inventory spans executor refinement, flat and logical representations,
history summaries, materialized inboxes, host fidelity, turn boundaries,
replay, revisions, migration routes, transport, peer convergence, ports,
retries, commit and recovery, mixed ordering, catch-up, forks, ownership,
client oracles, component wiring, table changes, time conversion, and field
editing. [^s12]

The inventory assigns each row a Q-number for lookup. For example, Q1 is
executor refinement, Q4 is history versus summary, and Q23 is a table
representation change. These identifiers name obligations, not theorem
statuses. Its relation vocabulary distinguishes seven kinds:

| Kind | Meaning | Inventory examples |
|---|---|---|
| E | Equality or the graph of a function | Replay; ownership shadow; table representation |
| S | Forward simulation, possibly with stuttering | Executor refinement; commit; recovery |
| B | Bisimulation up to a declared relation | History versus summary under future observations |
| L | Lens laws for a restricted update language | Field edits |
| Q | Lossy mapping with a declared kernel | A port's read view |
| T | Observation equality under certified schedule swaps | Peer convergence; materializer schedules |
| X | Actual environment behaviors contained in a model | Native adapters versus simulated faults |

These are the inventory's classifications, with X explicitly outside the
frame's representation squares. Q10 additionally compares routes made from
squares. Such a comparison is called a **2-cell**: it relates
transformations rather than individual states. [^s13] [^s14]

The distinction between E and S matters. Two implementations can each
simulate a nondeterministic specification that allows either `0` or `1`, yet
choose different results. The simulations establish containment in the
specification; equality between implementations needs an additional matching
or uniqueness argument. [^s15]

## 3.3 The generating set exposes what a proof must cover

Proving every component's favorite transition can leave the composite
operation uncovered. Two correct inbox edges do not establish a correct poll
that merges them: the merge can duplicate an item, lose a reason, or advance
a cursor past unread input. Generators therefore belong to the composite
semantic machine, including synchronization and shared resource protocols.
[^s16] [^s17]

**G0 establishes entry.** It relates the initial states or the states at a
conversion boundary and establishes their admissibility. Conversion has its
own proof even when all subsequent transitions are covered. [^s8]

**G1 matches a transition kind.** For every admitted instance of that kind,
related states take matching steps or words, remain admissible and related,
and preserve the named observations. Successful updates, refusals, and
emitted effects all belong to this obligation. [^s18] [^s10]

**G1q exposes loss.** It is G1 specialized to a lossy map `q`. **Snapshot
factorization** means each retained observation can be computed from `q(s)`.
The **kernel** of `q` relates states with the same image. **Future
congruence** means those states continue to have the same image after every
promised future operation. A read-only snapshot contract need not promise
congruence under every command. [^s19]

**G2 certifies a swap.** For a declared-independent pair of transition
occurrences, both routes are legal, the occurrences retain their meaning,
and the endpoints agree under a declared, future-closed relation.
Enabledness, effects, allocator changes, scheduler consequences, and the
observation contract are part of the certificate. [^s2] [^s20]

This gives G0, G1, and G2, with G1q a named variant of G1. It does not turn
every route equation into a swap: duplicate absorption, comparing `f` with
`ff`, changes word length and needs its own equation. [^s21] [^s22]

## 3.4 Compose steps, swaps and representation changes

To **paste** squares is to compose their local claims. There are three uses
here: extend a step correspondence along a run, compose permitted swaps, and
combine a representation change with rescheduling.

Composition fails when an author silently changes the contract between
pieces. A hidden difference may reappear after another input, a matching
word may change label identities, or a representation change may destroy an
independence claim. The pasting rules inherit these obligations; they do not
discharge them. [^s23] [^s24]

**Step pasting extends G1 along a word.** The COHERENCE design note calls
this vertical pasting. The empty word preserves the starting relation; each
next label applies its square. In the pinned Lean code, `Sq.paste` proves
this with `interp` mapping labels to target words. `Sq.paste_cover` adds a
catalogue premise: every label used by the word belongs to the cases whose
squares were supplied. [^s25]

That coverage premise has teeth. `uncovered_catalogue_holds` covers the
one-case catalogue, while `uncovered_case_fails` proves failure for a word
using the omitted case. A list of dispatch cases is useful only when
executions are shown to stay within it. [^s26]

**Swap pasting extends G2 along a sequence of swaps.** The design note calls
this horizontal pasting. A **Mazurkiewicz trace** groups words that differ
only by exchanges of adjacent independent labels. Those exchanges may occur
inside a longer word. Godefroid's Theorem 3.10 establishes equal reached
states for executable words in the same trace under a valid dependency
relation. [^s27] [^s28]

In Lean, `TraceEq` records those swaps and their equivalence closure;
`trace_run` derives equal partial runs from `Diamonds`. Its equality is
stronger than equality of selected endpoint observations: it includes
agreement on failure of the two-step run. [^s29] [^s30]

**Mixed pasting combines representation change with rescheduling.** For the
general schema, reading relational composition left to right, the proposed
compatibility condition is:

```text
R_AB ; approx_B  subset-of  approx_A ; R_AB
```

If `a R_AB b` and `b approx_B b'`, there must be an `a'` equivalent to `a`
with `a' R_AB b'`. The label interpretation also needs to preserve the
declared swaps; the relation inclusion alone is insufficient. [^s31]

The pinned Lean theorem `coherence` proves a narrower, concrete shape: one
representation edge, partial deterministic transitions, exact implementation
diamonds, a related start, and a successful run. It first reschedules on the
implementation side, then pastes the correspondence. It does not establish
the full mixed schema for arbitrary endpoint equivalences and dynamic
residuals. [^s32]

Induction along words, relational composition, and transitivity of
observation equality are reusable once their premises hold. Converter
correctness, future closure, legal enabledness, compatible labels, and
adequate observations are earned for the instance. [^s33]

Pairwise certificates suffice for an explicit finite sequence of valid
swaps. Stronger claims about a consistent dynamic partial order or
route-independent occurrence identities need residual consistency: the two
three-swap routes reversing three occurrences must transport those
identities consistently. [^s34]

## 3.5 Different machines can share the decisive state

The fn2 coherence draft was wrong to propose different machines as an
independence condition. Its counterexample has a listener awaiting an Accept
result and an occupied echo row awaiting a Close result. Accept-first
refuses the new connection; close-first releases a row before admission. The
shared allocator makes the order observable. [^s35]

The pinned implementation still exposes the shared state directly.
`fn2-listener-admit` reads the free head and active count, enters closing
when capacity is unavailable, and updates the allocator on admission.
`fn2-connection-release` can return a non-retired row to that free chain and
decreases the active count. [^s36] [^s37]

The Lean abstraction makes the failed claim small enough to inspect. It
starts with free count zero, one occupied row, and no admissions:

| Route | Admissions observed |
|---|---:|
| accept; close | 0 |
| close; accept | 1 |

`acceptClose_routes_disagree` proves both results and the words' trace
equivalence under the false `differentMachine` declaration. [^s38] [^s39]

The other teeth isolate the missing premise. `acceptClose_not_diamond`
refutes the diamond; `acceptClose_footprint_dependent` identifies the shared
free count; `acceptClose_without_g2` packages a correspondence with G1 and
its observation edge, a related start, trace equivalence, and a successful
run, while proving that the coherence conclusion fails. [^s40] [^s41]

A footprint declaration earns independence only when the implementation
respects it. `Action.Respects` says guards and written values depend on
declared reads, and positions outside declared writes remain unchanged.
`footIndep` excludes either action writing what the other reads or writes.
Under those premises, `footprint_independent` proves commutation and
preservation of enabledness. [^s42] [^s43]

Equal two-step partial runs alone do not establish full independence: two
actions that disable each other can both produce a failed composite run.
`IndependentDiamonds` adds the enabledness clause. This matches Godefroid's
requirement that independent transitions neither enable nor disable one
another. [^s44] [^s45]

The ACL2 companion, `examples/assured/diamond.lisp`, makes the same argument
in three parts:

1. `footprint-diamond` proves the generic case: two actions that each
   read and write only one position commute when their positions differ,
   whatever each computes there.
2. From free count 0, one occupied row and no admissions, the book
   evaluates accept-then-close to 0 admissions and close-then-accept to 1.
   `accept-close-not-diamond` proves that the routes differ even though
   the actions belong to different machines. Their declared write sets
   overlap at the free count, so the footprint test classifies them as
   dependent.
3. Two counter increments at different positions pass the footprint test.
   `bump-diamond` obtains their commutation theorem by functional
   instantiation of the generic result. [^s46]

The failed accept/close diamond refutes the independence declaration. It
does not identify a server defect: admission may legitimately depend on
whether reclamation ran first. [^s47]

A failed diamond can require a design decision. For live publication against
durable notification, fn2's analysis found different delivered orders; a
declared merge order then creates a G1 obligation for delivery. The useful
outcome is a decision plus generators: preserve the relevant order or
explicitly narrow the contract, then prove the resulting steps. [^s48] [^s49]

## 3.6 Article numbers prevent one universal observation class

A comparator that discards local article numbers can pass peer convergence
while missing a WIRE difference. In fn2's analysis, two POSTs to the same
group exchange assigned numbers when their commit order changes. NNTP
replies can contain those numbers, so preserving connection bytes and
forgetting article numbering are incompatible promises. [^s50]

For Q1 and WIRE, the relevant contract preserves reply bytes, making those
POSTs dependent. Q12 can instead observe validated facts and forget local
numbering. That narrower observation can support a convergence claim without
establishing equality of the wire interactions. [^s51]

The same caution applies to resource abstractions. A model of acquisition
orders can help organize exploration while forgetting payloads, article
numbers, faults, and fragmentation. Covering its resource components does
not establish coverage of the richer observation contract. [^s52]

## 3.7 In ACL2, prove the step cases and instantiate the fold

A failed functional instance may expose a false contract rather than a
missing hint. The read-state teeth prove the step obligation false for
equal-count states. That theorem supplies the counterexample independently
of the failed proof attempt. [^s4]

The manual states the obligation: "before such a lemma instance can be used,
the system will generate proof obligations" from the substituted supporting
constraints. Functional instantiation reuses a theorem after those
obligations are discharged. [^s53]

`fold-contract.lisp` introduces two initializers, two step functions, two
observers, admissibility predicates, and `fc-rel` in an `encapsulate`. Its
exported constraints establish initialization, step preservation, and
observation agreement. The local witnesses demonstrate that the constraints
are satisfiable. [^s54] [^s55]

The generic induction is this complete event, in that book's context:

```lisp
(defthm fc-rel-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))
```

Its companion `fc-obs-fold` derives observation equality after the suffix.
The relation theorem starts from any admissible related pair; applying it
from initialization or a converter additionally uses G0. [^s54]

The read-state instance supplies one preservation lemma for each event kind,
including malformed events. For example, its complete `:read` case is:

```lisp
(defthm rs-same-reads-of-read
  (implies (and (rs-s-ok s) (rs-same-reads h s)
                (rs-eventp e) (eq (car e) :read))
           (rs-same-reads (rs-h-step h e) (rs-s-step s e)))
  :hints (("Goal"
           :expand ((rs-same-reads (rs-h-step h e) (rs-s-step s e)))
           :use ((:instance rs-same-reads-necc
                            (n (rs-same-reads-witness (rs-h-step h e)
                                                      (rs-s-step s e))))))))
```

The cases combine in `rs-same-reads-of-step`; observation agreement and
initialization are proved separately. [^s56]

The instance then obtains the suffix theorem by replacing the contract's
functions, including its derived folds:

```lisp
(defthm rs-summary-adequate
  (implies (and (rs-h-ok h) (rs-s-ok s) (rs-same-reads h s))
           (and (rs-same-reads (rs-h-fold h j) (rs-s-fold s j))
                (equal (rs-h-obs (rs-h-fold h j) q)
                       (rs-s-obs (rs-s-fold s j) q))))
  :hints (("Goal"
           :in-theory (disable rs-h-ok rs-s-ok rs-h-obs rs-s-obs)
           :use ((:functional-instance fc-rel-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))
                 (:functional-instance fc-obs-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))))))
```

The converter theorem `rs-summarize-related` remains separate. [^s56]

That contract matches one event on each side. A fused executor can match one
step against several reference steps. The target side of the square
therefore needs a word of labels.

`examples/assured/square-paste.lisp` proves this form once in an
`encapsulate`. Its step constraint is `(sq-rel a b) => (sq-rel (sq-a-step a
l) (sq-b-run b (sq-h l)))`. Here `sq-h` maps a source label to a reference
word. `sq-paste` extends the relation to runs; `sq-paste-obs` gives
observation agreement. [^s3]

The concrete instance is a small executor-refinement example:

| Side | State | Step |
|---|---|---|
| Fused | Per-connection byte counts and a cached total | `(:recv2 k n m)` receives two chunks at once |
| Reference | Per-connection byte counts; the observer recomputes the total | `(:bump k n)` adds one chunk |

`fused-h` maps `(:recv2 k n m)` to `((:bump k n) (:bump k m))`. The instance
proves `fused-step-square` and `fused-edge`, using helper lemmas about
counts and updates. `fused-refines-reference` then follows by functional
instantiation, with no new induction for the whole-run result. [^s3]

The negative control omits the second chunk from the cached total. The book
evaluates disagreeing totals after one receive, then proves
`fused-step-bad-breaks-square`: the mutant violates the step obligation at
an initially related pair. [^s3]

## 3.8 TRACE checks independent selection with shared handlers

TRACE can pass a machine bug reproduced by both sides. Review S2 identified
this limitation: the reference shares harvesting and machine handlers with
the implementation. Its independent contribution is selection order,
including the calendar, queues, and observation order. [^s57]

At `127f7b877`, `fn2-check-trace-turn` keeps both cores across turns,
imports the common adapter boundary, checks the pre-state difference, runs
`fn2-ref-turn` and `fn2-turn`, and compares the resulting states and
`(status obs visits actions)`. A difference returns `(:fail :trace ...)` and
prints `TRACE DIFFERENCE` with its diagnostic. [^s58]

The scheduler comparison covers the literal calendar, cursor, runnable
count, service flags, per-principal FIFO contents, and intrusive links.
`fn2-representation-relation` means that neither the scheduler comparison
nor the core comparison reports a difference. [^s59] [^s60]

The shared calls are visible in `fn2-ref-transition`: harvesting and
observation dispatch, clock updates, grants, wake issuance, and machine
execution reuse implementation functions. Therefore TRACE gives differential
evidence about their scheduling and composition, without independently
validating those functions' semantics. [^s61]

The named `fn2-turn-refinement` is a `defthm-owed` statement at this pin. It
includes well-formedness, result equality, the post-state relation, and
explicit action and work bounds. A passing turn comparison does not prove
that universal statement or its accounting conclusions. [^s62]

Lean's composition theorem also leaves the ACL2 premises outstanding. The
metatheory document explicitly treats its license as an implication: it
neither interprets the ACL2 formulas nor converts a checked, unproved
instance into a discharged obligation. [^s63]

## 3.9 What the squares leave outside their conclusion

A sound composition theorem can be overclaimed without any false lemma: one
can apply it to a physical device, an eventual response, or an unexamined
schedule that its premises never covered. The boundary of the claim belongs
beside the square. [^s64]

**X rows remain environmental claims.** Simulation into a nondeterministic
fault model is a mathematical containment result. Establishing that real
disks, networks, and adapters satisfy that model needs separate evidence;
native experiments do not prove universal containment. [^s65]

**Finite-prefix equality does not establish liveness or cost.** Eventual
replies need progress assumptions. Visitation and resource bounds need
explicit accounting, and wall-time performance needs measurement. Two routes
returning equal observations can have different costs. [^s66] [^s67]

**Propositional squares do not determine transported data.** In the pinned
Lean model, `Sq` is a proposition. Such squares are called **thin**: two
proofs of the same square are equal by proof irrelevance. `Sq.interchange`
uses that property. Routes that choose position maps, converted cuts,
occurrence identities, or loss descriptors need agreement on that data
separately. [^s68] [^s69]

**Bounded checks refute instances within their explored domain.** A passing
continuation cannot prove future closure; passing diamonds do not authorize
pruning schedules. The proposed generator mode separates checking local
obligations from reaching states and reports its finite input domain and
horizon explicitly. [^s70]

**Composition soundness and completeness are different claims.** Soundness
says that valid generators compose into valid diagrams. The further claim
that every intended interchangeable route is connected by those generators
remains a separate conjecture. The pinned Lean development explicitly does
not claim it. [^s71] [^s72]

[Part 3 contents](../README.md) | [Previous chapter](02-simulation-and-checkers.md) | [Next chapter](04-certify-cost.md)

[^s1]: [fn: fn2/docs/design/COHERENCE.md:25 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L25).

[^s2]: [fn: fn2/docs/design/COHERENCE.md:94 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L94).

[^s3]: [example: examples/assured/square-paste.lisp] [Source](../../examples/assured/square-paste.lisp).

[^s4]: [example: examples/transport/read-state-teeth.lisp] [Source](../../examples/transport/read-state-teeth.lisp).

[^s5]: [fn: fn2/docs/design/COHERENCE.md:128 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L128).

[^s6]: [fn: fn2/meta/Fn2/Square.lean:172 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L172).

[^s7]: [fn: fn2/meta/Fn2/Square.lean:79 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L79).

[^s8]: [fn: fn2/docs/design/COHERENCE.md:91 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L91).

[^s9]: [fn: fn2/docs/design/COHERENCE.md:231 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L231).

[^s10]: [fn: fn2/docs/design/COHERENCE.md:249 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L249).

[^s11]: [fn: fn2/docs/design/COHERENCE.md:48 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L48).

[^s12]: [fn: fn2/docs/design/COHERENCE.md:52 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L52).

[^s13]: [fn: fn2/docs/design/COHERENCE.md:35 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L35).

[^s14]: [fn: fn2/docs/design/COHERENCE.md:61 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L61).

[^s15]: [fn: fn2/docs/design/COHERENCE.md:295 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L295).

[^s16]: [fn: fn2/docs/design/COHERENCE.md:112 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L112).

[^s17]: [fn: fn2/docs/design/COHERENCE.md:167 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L167).

[^s18]: [fn: fn2/docs/design/COHERENCE.md:92 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L92).

[^s19]: [fn: fn2/docs/design/COHERENCE.md:168 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L168).

[^s20]: [fn: fn2/docs/design/COHERENCE.md:169 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L169).

[^s21]: [fn: fn2/docs/design/COHERENCE.md:96 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L96).

[^s22]: [fn: fn2/docs/design/COHERENCE.md:171 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L171).

[^s23]: [fn: fn2/docs/design/COHERENCE.md:260 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L260).

[^s24]: [fn: fn2/docs/design/COHERENCE.md:316 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L316).

[^s25]: [fn: fn2/meta/Fn2/Square.lean:178 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L178).

[^s26]: [fn: fn2/meta/Fn2/Coherence.lean:489 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L489).

[^s27]: [paper: mazurkiewicz1995-introduction-to-trace-theory.pdf, section 1.3]

[^s28]: [paper: godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf, section 3.2, Theorem 3.10]

[^s29]: [fn: fn2/meta/Fn2/Coherence.lean:59 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L59).

[^s30]: [fn: fn2/meta/Fn2/Coherence.lean:84 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L84).

[^s31]: [fn: fn2/docs/design/COHERENCE.md:264 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L264).

[^s32]: [fn: fn2/meta/Fn2/Coherence.lean:107 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L107).

[^s33]: [fn: fn2/docs/design/COHERENCE.md:307 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L307).

[^s34]: [fn: fn2/docs/design/COHERENCE.md:328 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L328).

[^s35]: [fn: fn2/docs/design/COHERENCE.md:145 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L145).

[^s36]: [fn: fn2/books/machines-a-run.lisp:81 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a-run.lisp#L81).

[^s37]: [fn: fn2/books/machines-a-run.lisp:128 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/machines-a-run.lisp#L128).

[^s38]: [fn: fn2/meta/Fn2/Coherence.lean:413 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L413).

[^s39]: [fn: fn2/meta/Fn2/Coherence.lean:441 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L441).

[^s40]: [fn: fn2/meta/Fn2/Coherence.lean:424 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L424).

[^s41]: [fn: fn2/meta/Fn2/Coherence.lean:449 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L449).

[^s42]: [fn: fn2/meta/Fn2/Coherence.lean:138 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L138).

[^s43]: [fn: fn2/meta/Fn2/Coherence.lean:206 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L206).

[^s44]: [fn: fn2/meta/Fn2/Coherence.lean:67 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L67).

[^s45]: [paper: godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf, section 3.1, Definition 3.1]

[^s46]: [example: examples/assured/diamond.lisp] [Source](../../examples/assured/diamond.lisp).

[^s47]: [fn: fn2/docs/design/COHERENCE.md:851 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L851).

[^s48]: [fn: fn2/docs/design/COHERENCE.md:731 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L731).

[^s49]: [fn: fn2/docs/design/COHERENCE.md:738 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L738).

[^s50]: [fn: fn2/docs/design/COHERENCE.md:161 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L161).

[^s51]: [fn: fn2/docs/design/COHERENCE.md:235 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L235).

[^s52]: [fn: fn2/docs/design/HIGHER-STRUCTURES.md:56 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/HIGHER-STRUCTURES.md#L56).

[^s53]: [:doc lemma-instance]

[^s54]: [example: examples/transport/fold-contract.lisp] [Source](../../examples/transport/fold-contract.lisp).

[^s55]: [:doc encapsulate]

[^s56]: [example: examples/transport/read-state-transport.lisp] [Source](../../examples/transport/read-state-transport.lisp).

[^s57]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:87 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L87).

[^s58]: [fn: fn2/sim/check-trace.lisp:5 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-trace.lisp#L5).

[^s59]: [fn: fn2/books/reference.lisp:172 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L172).

[^s60]: [fn: fn2/books/reference.lisp:223 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L223).

[^s61]: [fn: fn2/books/reference.lisp:92 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L92).

[^s62]: [fn: fn2/books/reference.lisp:248 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L248).

[^s63]: [fn: fn2/docs/design/LEAN-METATHEORY.md:32 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/LEAN-METATHEORY.md#L32).

[^s64]: [fn: fn2/docs/design/COHERENCE.md:808 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L808).

[^s65]: [fn: fn2/docs/design/COHERENCE.md:810 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L810).

[^s66]: [fn: fn2/docs/design/COHERENCE.md:130 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L130).

[^s67]: [fn: fn2/docs/design/COHERENCE.md:814 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L814).

[^s68]: [fn: fn2/meta/Fn2/Square.lean:134 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Square.lean#L134).

[^s69]: [fn: fn2/docs/design/COHERENCE.md:289 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L289).

[^s70]: [fn: fn2/docs/design/COHERENCE.md:750 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L750).

[^s71]: [fn: fn2/docs/design/COHERENCE.md:189 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L189).

[^s72]: [fn: fn2/meta/Fn2/Coherence.lean:43 @dddc32d34] [Source](https://github.com/emberian/fn/blob/dddc32d34/fn2/meta/Fn2/Coherence.lean#L43).
