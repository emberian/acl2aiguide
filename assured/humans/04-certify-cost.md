# 4. Keep generated proofs affordable

Generated proofs need a cost budget. Reusing a declaration across many
fields and tables also repeats its proof work; a broad rewrite or arithmetic
rule can make every later book slower. The practical pattern is to prove a
generic template once, instantiate narrow facts for each field, and keep the
broad rules disabled outside the proofs that need them. [^s1]

fn2 set a one-minute certification limit per book. Its repairs reduced the
sum of measured layer-A book times from 1,876 s to 284 s without changing
statements. This chapter explains the rule families responsible, the
templates and splits that reduced their cost, and why prover-step counts
alone did not reveal the problem. [^s2]

## 4.1 What goes wrong

**A generated family that matches everything.** fn2's `defcolumns` emitted,
for every numeric array column, a type-prescription and a linear rule about
`(nth i xs)` under that column's array predicate. Each rule matches every
`nth` term in every goal, whatever field it reads. The W1 report: "Hundreds
of field predicates matched any `(nth i xs)`. Accumulated persistence on the
physical type proof recorded 1,090,404 NTH frames, 1,084,764 useless;
unrelated array rules each made 13,724 unsuccessful attempts. This was
repeated irrelevant recognition, not inherent simulator work" [^s3]. With
that family as its main cause, the layer-A closure's slowest book took
902.39 s and the sum of its book times was 1,876 s [^s2].

**A generator that reopens the whole table for each field.** Before R5a's
third pass, a 41-field machine declaration took 104.72 s and allocated 21 GB
to certify; "The superlinear families were the raw/public setter WFP and
type proofs, which repeatedly expanded the entire table recognizer and shape
invariant" [^s4]. The sprint that first hit it measured "402 seconds / 85
GB" for one declaration [^s5].

**A step budget that does not see it.** In the same R5a pass, the composed
simulator book's prover steps fell from 2,567,776 to 2,453,093 while its
time rose from 666.13 s to 842.08 s: "the logs do not support attributing
all elapsed-time growth to the generic column template" [^s6]. Section 4.3
reproduces the effect in a certified book.

Every book certified, but a fifteen-minute certification delays every author
who needs to check an edit. Part 1's process chapter describes that
iteration cost (`humans/06-process.md`, "sizing proofs";
`fn-lessons/12-library-weight.md`).

## 4.2 The rule

Ember's rule, as the W1 commit records it: "no book should be over 1m"
[^s2]. W1 met it for the whole measured closure: "All 72 books of the
closure, measured fresh with two jobs: slowest sim-adapter-base 902.39 s ->
46.84 s; sim 315.81 -> 22.61 s; echo 213.59 -> 12.39 s; assembly 108.90 s ->
43.43 s as six section books ... Sum of book times 1,876 -> 284 s" [^s2].
The layer-A note keeps it as a standing limit: "R5b retains W1's one-minute
limit: all 73 books in the measured layer-A closure certify below 60 s on
the laptop with two jobs, including the new WORK controls. The maximum is
`sim/sim-adapter-base` at 48.16 s" [^s7].

Three properties make the rule work, and they are what to copy:

- **It is per book, not per closure.** A closure can grow; a book cannot.
  The rule forces the split (section 4.5) at the point where the next
  edit would otherwise cost minutes.
- **It is measured, fresh, by the CERTIFY-BOOK Time line.** W1's numbers
  "are ACL2's **CERTIFY-BOOK Time** summaries, not shell elapsed time or
  proof-load estimates", every book "forced fresh" [^s8]. Part 1 explains what that line covers
  (`fn-lessons/10-time-line-and-goal-theory.md`).
- **It is met without weakening anything.** W1: "No statement changed, no
  step limit raised, no skip-proofs" [^s2].
  A rule that can be met by deleting a theorem is a rule about theorems,
  not about time.

Performance of the served code is published, never a gate (fn2's law, and
this guide's: `humans/06-process.md`). Certify time is different: it is the
iteration loop of every author, and fn2 treats it as a limit.

## 4.3 Why the step counter did not catch it

`examples/assured/nth-cost.lisp` reproduces the family at a size that
certifies in about a second. A generator emits, per array column K, a
*generic* rule about `(nth i xs)` under `arr-pK` and a *specific* rule about
`(nth i (nth K r))`, the field it belongs to. The theorem `field-sum-bound`
bounds the sum of one entry from each of N fields; the book proves it once
with only the specific rules and once with both [^s9]. Measured at three
sizes:

| fields N | specific rules only | both families enabled |
|---:|---|---|
| 12 | 0.00 s, 1,164 steps | 0.04 s, 1,659 steps |
| 24 | 0.01 s, 2,292 steps | 0.50 s, 3,879 steps |
| 36 | 0.02 s, 3,420 steps | 2.07 s, 6,675 steps |

The table records the two DEFTHM summaries at each size. [^s10] Over these
three sizes, the specific proof's step count grows linearly with N; with
both families enabled, elapsed time grows about fiftyfold from N = 12 to N =
36. The step count does not track the time: at N = 36 the generic proof
takes a hundred times as long as the specific one for about twice the steps.
Where the extra time goes is not shown by the counters used here; what the
table shows is that the step count is not a proxy for it. A
`with-prover-step-limit` above 6,675 would admit both 36-field proofs
despite their roughly hundredfold time difference. A lower limit could
reject the slower proof; the experiment does not show that every step budget
misses it. Part 1's "steps ratchet" (`humans/06-process.md`) limits counted
work. These measurements show why elapsed time must be recorded alongside
it.

The tools that did find the family are the ones that count rule
applications: accumulated persistence (W1's "1,090,404 NTH frames, 1,084,764
useless") and per-event time in the certification output, read by event
family [^s3]. Accumulated persistence "is a statistic ... that helps you
identify the rules that are causing ACL2's search space to explode" [^s11];
`humans/01-logic-and-prover.md` section 1.7.1 shows how to run it.

## 4.4 Use broad facts to derive narrow facts, then disable them

W1's fix keeps the family and changes its scope: "`defcolumns` now uses them
while deriving the typed accessor API and then disables them
(fn2-columns-array-nth-runes); the field-specific facts stay enabled and the
generic ones remain available by hint" [^s2]. In the generator:

```lisp
; These array-predicate facts match every NTH, independent of its field.
; Use them while deriving the typed accessor API, then keep them available
; only by explicit hint. The field-specific RAW-NTH facts remain enabled.
(defun fn2-columns-array-nth-runes (fields) ...)
```

This excerpt names the rule-selection helper. [^s12] The expansion ends with
`(in-theory (disable ,wfp ,init ,@(fn2-columns-array-nth-runes fields)))`
[^s13]. The field-specific facts are stated about the exact term a reader
produces, `(nth i (nth K st))`, so each one is tried only on its own field
[^s14].

The same discipline appears twice more in W1: "tau disabled locally in sim
and echo and in one guard; the release-count recognizer kept closed;
fn2-sim-adapter-shape takes an open-core switch so composed calls keep
fn2-core-wfp closed" [^s2]. One owner-lookup guard "spent 32.12 of 36.61 s
in tau"; disabling tau there alone gave 2.72 s [^s15]. The common rule: **a
generator's broad facts are scaffolding for its own proofs; what it exports
enabled is the narrowest fact a consumer's goal will contain.**
`examples/assured/columns.lisp` follows it: its per-array NTH facts derive
the reader theorems and are disabled at the end of the expansion [^s16].

## 4.5 Generic templates: one proof, an instance per field

R5a's third pass replaced per-field proofs with instances of a template
proved once: "The fix proves column-length preservation once over a column
index, keeps each table's WFP opaque, and instantiates the type/shape facts
for one field" [^s17]. The measured curve, the sprint's machine schema at
three sizes [^s18]:

| storage fields | before | after |
|---:|---|---|
| 19 | 8.76 s, 2.6 GB allocated | 1.64 s, 0.76 GB |
| 29 | 30.42 s, 7.6 GB | 2.44 s, 1.2 GB |
| 41 | 104.72 s, 21.4 GB | 4.42 s, 1.9 GB |

The template in `columns.lisp` is an `encapsulate` over a constrained value
predicate, with its list facts proved once: [^s19]

```lisp
; One list template; each column instantiates it, without repeating induction.
(encapsulate (((fn2-columns-valuep *) => *))
 (local (defun fn2-columns-valuep (x) (natp x))))
(defun fn2-columns-valuesp (xs)
 (if (atom xs) (eq xs nil)
   (and (fn2-columns-valuep (car xs)) (fn2-columns-valuesp (cdr xs)))))
(defthm fn2-columns-valuesp-nth
 (implies (and (fn2-columns-valuesp xs) (natp i) (< i (len xs)))
          (fn2-columns-valuep (nth i xs))))
```

Each array column's facts are `:functional-instance` hints of it with the
column's predicate substituted [^s20]. Column lengths have "one
index-parametric update proof, just like types" [^s21].
`examples/assured/columns.lisp` uses the same template (`ac-valuesp-nth`,
`ac-valuesp-update`, `ac-valuesp-resize`, instantiated per column by
`ac-array-facts`) [^s16].

The pass also captured the generator's own theory: "Tables without extra
fields use a captured column proof theory locally, so prior machine kinds
and the larger core theory do not inflate each field proof" [^s17]. In the
book that is a `deftheory` taken at the end of `columns.lisp` and installed
`local`ly in each expansion [^s22]. Without it, the same 41-field
declaration in a world that had already loaded the core took 16.05 s; with
it, 5.91 s [^s5]. A generated proof that runs in the includer's theory costs
whatever the includer has accumulated.

The count of what a declaration emits is affine in its fields after the
pass: "456, 696 and 984 theorems for 19, 29 and 41 storage fields, exactly
`24 x storage-fields`" [^s23].

## 4.6 Specify the generator's cost contract and check its growth

fn2's metatheory plan writes the lesson down as a contract every generator
must keep, so that the next one does not need its own "pass 3":

```text
generated theorem count <= c0 + cF*F + cA*A + cH*H
generated prover steps  <= b0 + bF*F + bA*A + bH*H
```

for `F` storage or layout fields, `A` declared arms and handlers and `H`
core children, with constants per template version and toolchain [^s24]. The
plan proposes three rules: every generated proof runs in a pinned theory;
"Whole-table recognizers (`NAME-P`, `NAME-WFP`, `fn2-corep`, `fn2-core-wfp`)
are closed at their definition and opened only in their named bridges"; and
"at most **one linear-sized bridge per family**". It also proposes two gates
to detect violations: a structural gate that counts admitted expansion
events against the formula and refuses child-pair matrices, and a cost gate
of 10-, 20-, 32- and 64-field fixtures with "fixed affine prover-step
budgets ... (prover steps are deterministic; wall time is published, never a
gate, beside the binding W1 rule of no book over 60 s)" [^s25]. The fixtures
exist at `127f7b877` [^s26]; the gates do not.

Section 4.3 shows the limit of the second gate: deterministic step counts do
not track the elapsed cost of this rule family closely enough. The
measurements alone do not isolate all the additional work. Keep the per-book
one-minute limit alongside the step budget, as the plan requires.

**Kits.** The plan turns each per-declaration family into a kit proved once
(typed array contents, heterogeneous record type, column length, field
accessor facts, core-child frame, initialization countdown, operation
composition, frame per arm, layout field composition, the fold contract of
chapter 5, abstract-stobj obligations, run invariant), with the rule: "A
per-declaration theorem family is written **once**, over constrained
functions, and each declaration owes only an instance whose obligations are
its own definitions and applicability lemmas" [^s27]. One kit is fn's oldest
lesson in this form (`fn-lessons/22-def-loop.md`: "no instance induction, no
instance hint"). Its authors add the limit: "a template emitter is not a
trusted proof rule: ACL2 admits every resulting theorem" [^s28].

## 4.7 Splits: where a book is cut

**Split at real generation boundaries.** fn2's assembly expands every
registered machine and child into the core in one book; at 108.90 s it broke
the rule. W1 split it "at the same real generation boundaries:
index/directory -> core -> access -> callbacks -> dispatch -> reference.
Both public include paths remain. Review verified each original event form
exactly once and in its original order" [^s29]. The public book is now an
umbrella:

```lisp
(include-book "assembly-reference")
```

with the six sections chained by their own includes [^s30]. The group costs
43.43 s with the umbrella at 0.93 s [^s31]. This split preserved the event
forms and their order; the report checked that correspondence explicitly.

**Split a proof at a semantic stage.** The simulator's `fn2-sim-advance`
cost 593.22 s in its six preservation proofs. R5a's third pass split its
body "into flight and selection stages", gave "each stage the same six
preservation contracts", and proved the composition through those contracts:
50.79 s for the family [^s32]. The plan's operation-composition kit would
generate the composition, but "it does not find a good semantic stage
boundary by itself" [^s33].

**A split is not an excuse.** "Splitting books does not excuse growing
per-declaration proof work" [^s34]. fn's older rule, "Split a book over 800
lines at its seam" [^s35], is about reading; the one-minute rule is about
time; neither replaces the other.

## 4.8 The checklist

For a generator, before it emits its first theorem:

1. **Emit narrow facts enabled, broad facts disabled.** A rule whose
   left-hand side matches every `nth` (or every `car`, or every call of a
   generic accessor) is scaffolding: use it inside the expansion, disable
   it at the end, keep it available by hint [^s9].
2. **Prove the family once.** An `encapsulate` over constrained functions,
   instantiated per field by `:functional-instance` [^s16]; never a fresh induction per field.
3. **Pin the theory.** Capture the generator book's theory and install it
   locally in each expansion, so the includer's world does not change the
   generated proofs' cost.
4. **Close whole-state recognizers.** Open them only in named bridges;
   part 1's pitfall 7 is the same rule for hand-written books
   (`ai/00-pitfalls-first.md`).
5. **Measure at three sizes.** A declaration's cost at 10, 20 and 40
   fields shows its curve; one size shows nothing.
6. **Measure time and applications, not steps alone.** The step counter
   missed this family (section 4.3); accumulated persistence and per-event
   time did not.
7. **Keep the one-minute rule per book**, fresh, by the CERTIFY-BOOK
   line, met without weakening any statement.

[Part 3 contents](../README.md) | [Previous chapter](03-commuting-squares.md) | [Next chapter](05-transport.md)

[^s1]: [fn: fn2/books/columns.lisp:17-32, 223-238, 617 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L17).

[^s2]: [fn: commit message of 1fa1fe24b]

[^s3]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:17 @worktree, read 2026-10-29]

[^s4]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:208-216 @worktree, read 2026-10-29]

[^s5]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:214 @worktree, read 2026-10-29]

[^s6]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:227-229 @worktree, read 2026-10-29]

[^s7]: [fn: fn2/docs/a-pool-host-sim.md:498-500 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L498).

[^s8]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:9 @worktree, read 2026-10-29]

[^s9]: [example: examples/assured/nth-cost.lisp] [Source](../../examples/assured/nth-cost.lisp).

[^s10]: [measured: REPL driver generating the book's two theorems at N = 12, 24, 36 (the sum bounded by 2^60), the Time and "Prover steps counted" lines of each DEFTHM summary, ACL2 8.7, SBCL 2.6.8, laptop, 2026-10-29]

[^s11]: [:doc accumulated-persistence]

[^s12]: [fn: fn2/books/columns.lisp:223-238 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L223).

[^s13]: [fn: fn2/books/columns.lisp:617 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L617).

[^s14]: [fn: fn2/books/columns.lisp:505-522 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L505).

[^s15]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:21 @worktree, read 2026-10-29]

[^s16]: [example: examples/assured/columns.lisp] [Source](../../examples/assured/columns.lisp).

[^s17]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:216 @worktree, read 2026-10-29]

[^s18]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:208-212 @worktree, read 2026-10-29]

[^s19]: [fn: fn2/books/columns.lisp:17-25 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L17).

[^s20]: [fn: fn2/books/columns.lisp:191-213 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L191).

[^s21]: [fn: fn2/books/columns.lisp:45-54 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L45).

[^s22]: [fn: fn2/books/columns.lisp:564-567, 715-718 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/columns.lisp#L564).

[^s23]: [fn: fn2/docs/design/DSL-METATHEORY.md:375 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L375).

[^s24]: [fn: fn2/docs/design/DSL-METATHEORY.md:368-375 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L368).

[^s25]: [fn: fn2/docs/design/DSL-METATHEORY.md:377-382 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L377).

[^s26]: [fn: fn2/tests/columns-cost-unit-10.lisp, columns-cost-unit-20.lisp, columns-cost-unit.lisp @127f7b877]

[^s27]: [fn: fn2/docs/design/DSL-METATHEORY.md:323, 349-362 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L323).

[^s28]: [fn: fn2/docs/design/DSL-METATHEORY.md:323 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L323).

[^s29]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:25 @worktree, read 2026-10-29]

[^s30]: [fn: fn2/books/assembly.lisp:1-8 @127f7b877; fn: fn2/books/assembly-core.lisp:1-4 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/assembly.lisp#L1).

[^s31]: [fn: build/coordinator/fn2/lanes/a-quests/W1.REPORT.md:11 @worktree, read 2026-10-29]

[^s32]: [fn: build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:218-222 @worktree, read 2026-10-29]

[^s33]: [fn: fn2/docs/design/DSL-METATHEORY.md:386 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L386).

[^s34]: [fn: fn2/docs/design/DSL-METATHEORY.md:382 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/DSL-METATHEORY.md#L382).

[^s35]: [fn: docs/proof-style.md:411 @3bbfc4dca]
