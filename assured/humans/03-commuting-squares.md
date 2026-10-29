# 3. Every correctness claim as a commuting square

Equal answers now can conceal different answers after the next input.
In the guide's read-state example, histories containing `(:read 1)` and
`(:read 2)` both report one read article. After `(:read 1)`, their counts
differ. The theorem `rs-count2-rel-not-step-closed` exhibits the failure:
the proposed relation preserves today's observation but cannot support
tomorrow's substitution.
[example: examples/transport/read-state-teeth.lisp]

A commuting square makes that missing condition explicit. It names the
representations, the relation between them, the transitions that preserve
it, and the observations that relation protects. Its useful promise is
compositional: local preservation extends to executions under stated
premises. Environment fidelity, progress, and completeness of the chosen
generators remain separate claims.
[fn: build/coordinator/fn2/COHERENCE.md:25 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:128 @worktree, read 2026-10-29]

## 3.1 The square has a relation, an observation, and a loss

A relation chosen only because the current outputs match may fail its
first step obligation. The read-state counterexample gives the diagnostic
in semantic terms: related before, unrelated after one admitted event.
The repair is a relation strong enough to survive the promised transition
language, with observation agreement as a consequence.
[example: examples/transport/read-state-teeth.lisp]

Write a square as `(A, B, R, T, obs, kappa)`. Here `A` and `B` are state
representations; `R` relates their states; and each label in `T` has an
interpretation on both sides. An interpretation may be a word of steps,
including an empty word. `obs_A` and `obs_B` name the observations, while
`kappa` declares which observational differences the contract identifies.
Identity loss preserves the observations exactly.
[fn: build/coordinator/fn2/COHERENCE.md:25 @worktree, read 2026-10-29]
[fn: fn2/meta/Fn2/Square.lean:172 @dddc32d34]

The drawing and its three conditions are:

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
partial-transition version supplies a matching target execution whenever
the source transition succeeds.
[fn: build/coordinator/fn2/COHERENCE.md:25 @worktree, read 2026-10-29]
[fn: fn2/meta/Fn2/Square.lean:79 @dddc32d34]

The three conditions do different work. **Step** supports continuation.
**Edge** connects the internal relation to the user's contract. **Base**
establishes the relation at initialization or conversion. A correct step
theorem cannot repair a converter that starts outside the relation.
[fn: build/coordinator/fn2/COHERENCE.md:91 @worktree, read 2026-10-29]

Outputs and refusals belong in the matching condition. If the observation
is an emitted history, retain that history in the semantic state or carry
a monitor that observes it. Agreement at the final state cannot recover
a reply that differed earlier, and a matching word cannot hide an
externally distinguishable action prefix or crash cut.
[fn: build/coordinator/fn2/COHERENCE.md:231 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:249 @worktree, read 2026-10-29]

## 3.2 An inventory finds recurring obligations, not completed proofs

A table of squares can look like a table of guarantees even when its rows
are specifications, checked instances, or assumptions. The fn2 inventory
explicitly mixes those statuses. Its Q1-Q25 snapshot is evidence that the
shape recurs; it is not evidence that twenty-five correctness claims have
been proved.
[fn: build/coordinator/fn2/COHERENCE.md:48 @worktree, read 2026-10-29]

The inventory spans executor refinement, flat and logical representations,
history summaries, materialized inboxes, host fidelity, turn boundaries,
replay, revisions, migration routes, transport, peer convergence, ports,
retries, commit and recovery, mixed ordering, catch-up, forks, ownership,
client oracles, component wiring, table changes, time conversion, and
field editing.
[fn: build/coordinator/fn2/COHERENCE.md:52 @worktree, read 2026-10-29]

Its relation vocabulary distinguishes seven kinds:

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
frame's representation squares. Q10 additionally records a comparison
between routes: a 2-cell over squares.
[fn: build/coordinator/fn2/COHERENCE.md:35 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:61 @worktree, read 2026-10-29]

The distinction between E and S matters. Two implementations can each
simulate a nondeterministic specification that allows either `0` or `1`,
yet choose different results. The simulations establish containment in
the specification; equality between implementations needs an additional
matching or uniqueness argument.
[fn: build/coordinator/fn2/COHERENCE.md:295 @worktree, read 2026-10-29]

## 3.3 The generating set exposes what a proof must cover

Proving every component's favorite transition can leave the composite
operation uncovered. Two correct inbox edges do not establish a correct
poll that merges them: the merge can duplicate an item, lose a reason,
or advance a cursor past unread input. Generators therefore belong to
the composite semantic machine, including synchronization and shared
resource protocols.
[fn: build/coordinator/fn2/COHERENCE.md:112 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:167 @worktree, read 2026-10-29]

**G0 establishes entry.** It relates the initial states or the states at
a conversion boundary and establishes their admissibility. Conversion
has its own proof even when all subsequent transitions are covered.
[fn: build/coordinator/fn2/COHERENCE.md:91 @worktree, read 2026-10-29]

**G1 matches a transition kind.** For every admitted instance of that
kind, related states take matching steps or words, remain admissible and
related, and preserve the named observations. Successful updates,
refusals, and emitted effects all belong to this obligation.
[fn: build/coordinator/fn2/COHERENCE.md:92 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:249 @worktree, read 2026-10-29]

**G1q exposes loss.** It is G1 specialized to a lossy map `q`.
Snapshot factorization says each retained observation can be computed
through `q`. Future congruence says states identified by its kernel stay
identified under the promised future operations. A read-only snapshot
contract need not promise congruence under every command.
[fn: build/coordinator/fn2/COHERENCE.md:168 @worktree, read 2026-10-29]

**G2 certifies a swap.** For a declared-independent pair of transition
occurrences, both routes are legal, the occurrences retain their meaning,
and the endpoints agree under a declared, future-closed relation.
Enabledness, effects, allocator changes, scheduler consequences, and the
observation contract are part of the certificate.
[fn: build/coordinator/fn2/COHERENCE.md:94 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:169 @worktree, read 2026-10-29]

This gives G0, G1, and G2, with G1q a named variant of G1.
It does not turn every route equation into a swap: duplicate absorption,
comparing `f` with `ff`, changes word length and needs its own equation.
[fn: build/coordinator/fn2/COHERENCE.md:96 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:171 @worktree, read 2026-10-29]

## 3.4 Three pastings, with premises still attached

Composition fails when an author silently changes the contract between
pieces. A hidden difference may reappear after another input, a matching
word may change label identities, or a representation change may destroy
an independence claim. The pasting rules inherit these obligations;
they do not discharge them.
[fn: build/coordinator/fn2/COHERENCE.md:260 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:316 @worktree, read 2026-10-29]

**Vertical pasting extends G1 along a word.** The empty word preserves
the starting relation; each next label applies its square. In the pinned
Lean code, `Sq.paste` proves this with `interp` mapping labels to target
words. `Sq.paste_cover` adds a catalogue premise: every label used by the
word belongs to the cases whose squares were supplied.
[fn: fn2/meta/Fn2/Square.lean:178 @dddc32d34]

That coverage premise has teeth. `uncovered_catalogue_holds` covers the
one-case catalogue, while `uncovered_case_fails` proves failure for a word
using the omitted case. A list of dispatch cases is useful only when
executions are shown to stay within it.
[fn: fn2/meta/Fn2/Coherence.lean:489 @dddc32d34]

**Horizontal pasting extends G2 along a sequence of swaps.**
Mazurkiewicz traces identify words by the congruence generated by adjacent
independent letters. Godefroid's Theorem 3.10 establishes equal reached
states for executable words in the same trace under a valid dependency
relation.
[paper: mazurkiewicz1995-introduction-to-trace-theory.pdf, section 1.3]
[paper: godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf, section 3.2, Theorem 3.10]

In Lean, `TraceEq` records those swaps and their equivalence closure;
`trace_run` derives equal partial runs from `Diamonds`. Its equality is
stronger than equality of selected endpoint observations: it includes
agreement on failure of the two-step run.
[fn: fn2/meta/Fn2/Coherence.lean:59 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:84 @dddc32d34]

**Mixed pasting combines representation change with rescheduling.**
For the general schema, reading relational composition left to right,
the proposed compatibility condition is:

```text
R_AB ; approx_B  subset-of  approx_A ; R_AB
```

If `a R_AB b` and `b approx_B b'`, there must be an `a'` equivalent to
`a` with `a' R_AB b'`. The label interpretation also needs to preserve
the declared swaps; the relation inclusion alone is insufficient.
[fn: build/coordinator/fn2/COHERENCE.md:264 @worktree, read 2026-10-29]

The pinned Lean theorem `coherence` proves a narrower, concrete shape:
one representation edge, partial deterministic transitions, exact
implementation diamonds, a related start, and a successful run. It first
reschedules on the implementation side, then pastes the correspondence.
It does not establish the full mixed schema for arbitrary endpoint
equivalences and dynamic residuals.
[fn: fn2/meta/Fn2/Coherence.lean:107 @dddc32d34]

Induction along words, relational composition, and transitivity of
observation equality are reusable once their premises hold. Converter
correctness, future closure, legal enabledness, compatible labels, and
adequate observations are earned for the instance.
[fn: build/coordinator/fn2/COHERENCE.md:307 @worktree, read 2026-10-29]

Pairwise certificates suffice for an explicit finite sequence of valid
swaps. Stronger claims about a consistent dynamic partial order or
route-independent occurrence identities need residual consistency:
the two three-swap routes reversing three occurrences must transport
those identities consistently.
[fn: build/coordinator/fn2/COHERENCE.md:328 @worktree, read 2026-10-29]

## 3.5 Different machines can share the decisive state

The fn2 coherence draft was wrong to propose different machines as an
independence condition. Its counterexample has a listener awaiting an
Accept result and an occupied echo row awaiting a Close result.
Accept-first refuses the new connection; close-first releases a row
before admission. The shared allocator makes the order observable.
[fn: build/coordinator/fn2/COHERENCE.md:145 @worktree, read 2026-10-29]

The pinned implementation still exposes the shared state directly.
`fn2-listener-admit` reads the free head and active count, enters closing
when capacity is unavailable, and updates the allocator on admission.
`fn2-connection-release` can return a non-retired row to that free chain
and decreases the active count.
[fn: fn2/books/machines-a-run.lisp:81 @127f7b877]
[fn: fn2/books/machines-a-run.lisp:128 @127f7b877]

The Lean abstraction makes the failed claim small enough to inspect.
It starts with free count zero, one occupied row, and no admissions:

| Route | Admissions observed |
|---|---:|
| accept; close | 0 |
| close; accept | 1 |

`acceptClose_routes_disagree` proves both results and the words' trace
equivalence under the false `differentMachine` declaration.
[fn: fn2/meta/Fn2/Coherence.lean:413 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:441 @dddc32d34]

The other teeth isolate the missing premise.
`acceptClose_not_diamond` refutes the diamond;
`acceptClose_footprint_dependent` identifies the shared free count;
`acceptClose_without_g2` packages a correspondence with G1 and its
observation edge, a related start, trace equivalence, and a successful
run, while proving that the coherence conclusion fails.
[fn: fn2/meta/Fn2/Coherence.lean:424 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:449 @dddc32d34]

A footprint declaration earns independence only when the implementation
respects it. `Action.Respects` says guards and written values depend on
declared reads, and positions outside declared writes remain unchanged.
`footIndep` excludes either action writing what the other reads or writes.
Under those premises, `footprint_independent` proves commutation and
preservation of enabledness.
[fn: fn2/meta/Fn2/Coherence.lean:138 @dddc32d34]
[fn: fn2/meta/Fn2/Coherence.lean:206 @dddc32d34]

Equal two-step partial runs alone do not establish full independence:
two actions that disable each other can both produce a failed composite
run. `IndependentDiamonds` adds the enabledness clause. This matches
Godefroid's requirement that independent transitions neither enable nor
disable one another.
[fn: fn2/meta/Fn2/Coherence.lean:67 @dddc32d34]
[paper: godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf, section 3.1, Definition 3.1]

`examples/assured/diamond.lisp` is the ACL2 companion. It proves the
generic diamond once, `footprint-diamond`: two actions that each read and
write one position, at different positions, commute whatever they compute
there. It then evaluates accept and close from the start state (free count
0, one occupied row, nothing admitted): accept-then-close admits 0 and
close-then-accept admits 1, and `accept-close-not-diamond` is the theorem
that the two routes differ, although the two actions belong to different
machines. The footprint declaration classifies the pair as dependent,
their write sets meeting at the free count, so no diamond is claimed for
it; two counter bumps at different positions are declared independent and
get their diamond by functional instance of the generic one
(`bump-diamond`) [example: examples/assured/diamond.lisp]. The negative
result is a refuted independence declaration, not a server defect:
admission may legitimately depend on whether reclamation ran first
[fn: build/coordinator/fn2/COHERENCE.md:851 @worktree, read 2026-10-29].

A failed diamond can require a design decision. For live publication
against durable notification, fn2's analysis found different delivered
orders; a declared merge order then creates a G1 obligation for delivery.
The useful outcome is a decision plus generators: preserve the relevant
order or explicitly narrow the contract, then prove the resulting steps.
[fn: build/coordinator/fn2/COHERENCE.md:731 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:738 @worktree, read 2026-10-29]

## 3.6 Article numbers prevent one universal observation class

A comparator that discards local article numbers can pass peer convergence
while missing a WIRE difference. In fn2's analysis, two POSTs to the same
group exchange assigned numbers when their commit order changes.
NNTP replies can contain those numbers, so preserving connection bytes
and forgetting article numbering are incompatible promises.
[fn: build/coordinator/fn2/COHERENCE.md:161 @worktree, read 2026-10-29]

For Q1 and WIRE, the relevant contract preserves reply bytes, making
those POSTs dependent. Q12 can instead observe validated facts and forget
local numbering. That narrower observation can support a convergence
claim without establishing equality of the wire interactions.
[fn: build/coordinator/fn2/COHERENCE.md:235 @worktree, read 2026-10-29]

The same caution applies to resource abstractions. A model of acquisition
orders can help organize exploration while forgetting payloads, article
numbers, faults, and fragmentation. Covering its resource components
does not establish coverage of the richer observation contract.
[fn: build/coordinator/fn2/HIGHER-STRUCTURES.md:56 @worktree, read 2026-10-29]

## 3.7 In ACL2, prove the step cases and instantiate the fold

A failed functional instance may expose a false contract rather than a
missing hint. The read-state teeth prove the step obligation false for
equal-count states. That theorem supplies the counterexample independently
of the failed proof attempt.
[example: examples/transport/read-state-teeth.lisp]

The manual states the obligation: "before such a lemma instance can be
used, the system will generate proof obligations" from the substituted
supporting constraints. Functional instantiation reuses a theorem after
those obligations are discharged.
[:doc lemma-instance]

`fold-contract.lisp` introduces two initializers, two step functions, two
observers, admissibility predicates, and `fc-rel` in an `encapsulate`.
Its exported constraints establish initialization, step preservation,
and observation agreement. The local witnesses demonstrate that the
constraints are satisfiable.
[example: examples/transport/fold-contract.lisp]
[:doc encapsulate]

The generic induction is this complete event, in that book's context:

```lisp
(defthm fc-rel-fold
  (implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2))
           (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))
  :hints (("Goal" :induct (fc-fold2-induct s1 s2 j))))
```

Its companion `fc-obs-fold` derives observation equality after the suffix.
The relation theorem starts from any admissible related pair; applying
it from initialization or a converter additionally uses G0.
[example: examples/transport/fold-contract.lisp]

The read-state instance supplies one preservation lemma for each event
kind, including malformed events. For example, its complete `:read` case
is:

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
initialization are proved separately.
[example: examples/transport/read-state-transport.lisp]

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

The converter theorem `rs-summarize-related` remains separate.
[example: examples/transport/read-state-transport.lisp]

That contract matches one event on each side. A fused executor matches
one of its steps against several reference steps, so the square must allow
a word on the reference side. `examples/assured/square-paste.lisp` proves
that form once: in an `encapsulate`, the step constraint is
`(sq-rel a b) => (sq-rel (sq-a-step a l) (sq-b-run b (sq-h l)))`, where
`sq-h` sends a label to a word of reference labels, and `sq-paste` and
`sq-paste-obs` extend it to every word of labels, observations included.
Its instance is Q1's shape in miniature: per-connection byte counts with a
cached total on the fused side, whose label `(:recv2 k n m)` takes two
chunks in one step; per-connection counts only on the reference side,
whose `(:bump k n)` adds one chunk and whose total is recomputed by the
observation; `fused-h` sends `(:recv2 k n m)` to the two-step word
`((:bump k n) (:bump k m))`. The instance pays for one step lemma
(`fused-step-square`) and one edge lemma (`fused-edge`), and
`fused-refines-reference` is a functional instance with no induction of
its own. Its tooth is a fused step that forgets the second chunk in its
cached total: the totals disagree after one receive (evaluated), and
`fused-step-bad-breaks-square` proves the mutant's step obligation false
at a related pair [example: examples/assured/square-paste.lisp].

## 3.8 TRACE checks independent selection with shared handlers

TRACE can pass a machine bug reproduced by both sides. Review S2
identified this limitation: the reference shares harvesting and machine
handlers with the implementation. Its independent contribution is
selection order, including the calendar, queues, and observation order.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]

At `127f7b877`, `fn2-check-trace-turn` keeps both cores across turns,
imports the common adapter boundary, checks the pre-state difference,
runs `fn2-ref-turn` and `fn2-turn`, and compares the resulting states and
`(status obs visits actions)`. A difference returns `(:fail :trace ...)`
and prints `TRACE DIFFERENCE` with its diagnostic.
[fn: fn2/sim/check-trace.lisp:5 @127f7b877]

The scheduler comparison covers the literal calendar, cursor, runnable
count, service flags, per-principal FIFO contents, and intrusive links.
`fn2-representation-relation` means that neither the scheduler comparison
nor the core comparison reports a difference.
[fn: fn2/books/reference.lisp:172 @127f7b877]
[fn: fn2/books/reference.lisp:223 @127f7b877]

The shared calls are visible in `fn2-ref-transition`: harvesting and
observation dispatch, clock updates, grants, wake issuance, and machine
execution reuse implementation functions. Therefore TRACE gives
differential evidence about their scheduling and composition, without
independently validating those functions' semantics.
[fn: fn2/books/reference.lisp:92 @127f7b877]

The named `fn2-turn-refinement` is a `defthm-owed` statement at this pin.
It includes well-formedness, result equality, the post-state relation,
and explicit action and work bounds. A passing turn comparison does not
prove that universal statement or its accounting conclusions.
[fn: fn2/books/reference.lisp:248 @127f7b877]

Lean's composition theorem also leaves the ACL2 premises outstanding.
The metatheory document explicitly treats its license as an implication:
it neither interprets the ACL2 formulas nor converts a checked,
unproved instance into a discharged obligation.
[fn: build/coordinator/fn2/LEAN-METATHEORY.md:32 @worktree, read 2026-10-29]

## 3.9 What the squares leave outside their conclusion

A sound composition theorem can be overclaimed without any false lemma:
one can apply it to a physical device, an eventual response, or an
unexamined schedule that its premises never covered. The boundary of the
claim belongs beside the square.
[fn: build/coordinator/fn2/COHERENCE.md:808 @worktree, read 2026-10-29]

**X rows remain environmental claims.** Simulation into a nondeterministic
fault model is a mathematical containment result. Establishing that real
disks, networks, and adapters satisfy that model needs separate evidence;
native experiments do not prove universal containment.
[fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29]

**Finite-prefix equality does not establish liveness or cost.**
Eventual replies need progress assumptions. Visitation and resource bounds
need explicit accounting, and wall-time performance needs measurement.
Two routes returning equal observations can have different costs.
[fn: build/coordinator/fn2/COHERENCE.md:130 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:814 @worktree, read 2026-10-29]

**Thin squares do not settle data-carrying 2-cells.** In the pinned Lean
model, `Sq` is a proposition and `Sq.interchange` follows by proof
irrelevance. Routes that choose position maps, converted cuts, occurrence
identities, or loss descriptors need agreement on that data separately.
[fn: fn2/meta/Fn2/Square.lean:134 @dddc32d34]
[fn: build/coordinator/fn2/COHERENCE.md:289 @worktree, read 2026-10-29]

**Bounded checks refute instances within their explored domain.**
A passing continuation cannot prove future closure; passing diamonds do
not authorize pruning schedules. The proposed generator mode separates
checking local obligations from reaching states and reports its finite
input domain and horizon explicitly.
[fn: build/coordinator/fn2/COHERENCE.md:750 @worktree, read 2026-10-29]

**Generated soundness is not completeness.** The theorem says valid
generators compose. The further claim that every intended interchangeable
route is connected by those generators remains a separate conjecture.
The pinned Lean development explicitly does not claim it.
[fn: build/coordinator/fn2/COHERENCE.md:189 @worktree, read 2026-10-29]
[fn: fn2/meta/Fn2/Coherence.lean:43 @dddc32d34]
