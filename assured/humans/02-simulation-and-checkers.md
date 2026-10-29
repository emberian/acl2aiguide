# 2. Build a simulation gate that checks behavior

A simulation gate should answer three questions: what behavior ran, what
evidence was checked, and whether a detected failure reached the process
exit status. fn2 uses replayable runs, independent monitors and mutation
controls to test those links. A **gate** here is a check whose failure
blocks acceptance of a change. [^s1] [^s2] [^s3]

A simulator can exercise faults, print coverage, and exit successfully while
its gate has checked the wrong thing. fn2 did this: fault draws counted as
coverage before their effects occurred; a differential test comparing two
implementations exempted disagreements it had already found; selected
surface tests skipped without failing the process. Each failure let a
successful test result conceal missing or contrary evidence about the
implementation. [^s4] [^s5] [^s6]

The starting point is [section
5.7](../../humans/05-high-performance.md#57-tigerstyle-in-acl2): "a seeded
generator, a bounded event list, and a loop that checks the invariant after
every step and answers the first violation." This chapter develops the gate
around that loop: evidence of exercised faults, independent observations,
and controls that distinguish a correct implementation from a broken one.
[^s7]

The TigerBeetle background stays in section 5.7. Its distinction between
assertions inside the implementation and additional simulator checkers is
the useful starting distinction here. [^s8]

## 2.1 Put the simulated environment in the logic

A second environment model can disagree with the simulator that supplies the
test evidence. fn2's decision `A-SIM-IN-LOGIC` addresses that seam: the
simulator evaluates the environment model itself, so later proofs can refer
to the same definitions instead of introducing another model. [^s9]

The concrete arrangement is a simulator stobj separate from the core. Its
declaration contains rows for pending operations (called flights), nested
network and storage stobjs, PRNG words, clocks, fault state, replay
metadata, and an observation ring. These are explicit inputs and state for
the simulated environment. [^s10]

This does not put destructive assignment into the logical meaning. The
manual says, "From the logical perspective, a single-threaded object is an
ordinary ACL2 object," and gives the restriction: "Updates to the object
must be sequentialized." The simulator threads its state through its calls
accordingly. [^s11] [^s12]

The distinction between logic and verified guards matters here. The design
document says the simulator and checkers are guard-verified; that blanket
claim is too broad at this revision. `fn2-check-trace-turn` and
`fn2-check-own-parts` explicitly declare `:verify-guards nil`. Describe the
implemented boundary, rather than inheriting the document's stronger claim.
[^s13] [^s14] [^s15]

The chapter's small example uses ordinary lists and scalar arguments. It
isolates one echo connection, seeded faults, and competing checkers; it does
not reproduce fn2's nested stobj implementation. [^s7]

## 2.2 Replay needs a run description; exploration needs new seeds

A fixed acceptance seed can keep a regression reproducible while exploring
exactly yesterday's schedules. REVIEW-SINS T3 found fixed seeds throughout
fn2 and prescribed two modes: retain the acceptance seeds, and add a swarm
mode whose command-line or clock-derived seed is printed before the run.
[^s16]

fn2 uses xoshiro128** with four explicit state words. `fn2-prng-next`
returns the generated word and successor words; `fn2-sim-random` stores
those successors in the simulator. The replay description includes profile,
seed, observation order, fault choices, and revision. [^s17] [^s12] [^s18]

At the pinned revision, the A4 driver prints and flushes its mode and seed
before loading scenarios. It also regenerates the revision record before
loading them. This repairs the stale-revision failure described by T2.
[^s19] [^s20]

The fixed branch runs the pool campaigns and the echo workload with their
specified seeds. `FN2_SWARM=1` selects a fresh runtime seed;
`FN2_SWARM_SEED=<decimal>` supplies one for replay. The swarm branch is a
shorter campaign, not the fixed acceptance branch under another label.
[^s21] [^s22]

The example uses xorshift32, not fn2's xoshiro128**. Its replay assertion is
exactly this: [^s7]

```lisp
(assert-event (equal (mv-list 5 (run-seed 73 12 :broad nil))
                     (mv-list 5 (run-seed 73 12 :broad nil))))
```

That compares identical calls; it does not pin a stored fingerprint across
edits. The later mutant assertion pins a specific failure value. Do not turn
the example's replay comment into a stronger regression claim than its
forms. [^s7]

## 2.3 Count a fault when its effect occurs

A selected fault may do nothing. REVIEW-SINS S1 found that fn2 incremented
coverage when drawing a class, before determining whether it applied to the
next flight. A storage read error selected during a receive could therefore
help satisfy the coverage assertion without exercising that error. [^s4]

The R5d repair changed the order: select the pending operation, choose fault
classes applicable to its kind and stage, attempt the effect, and count a
**landing** only when that effect occurs. `fn2-sim-advance` selects the
flight before calling `fn2-sim-choose-flight-fault`; selection spends fault
budget without incrementing the landing counter. [^s23] [^s24] [^s25]

Applicability is not success. The physical landing predicate checks the
result: a short transfer requires `:ok` and a count below the requested
length; a lying fence requires a dirty fence and the lying behavior. The
counter is updated after the physical operation returns. [^s26] [^s27]

In the example, a one-byte remainder cannot have a positive short send. The
candidate list excludes that class before drawing: [^s7]

```lisp
(defun applicable (remaining)
  (declare (xargs :guard (natp remaining)))
  (if (<= 2 remaining) '(:short :delay :reset) '(:delay :reset)))

(defun choose-fault (profile remaining rng)
  (declare (xargs :guard (and (natp remaining) (natp rng))))
  (let* ((cands (applicable remaining))
         (rng (xorshift32 rng))
         (class (nth (modn rng (len cands)) cands))
         (rng (xorshift32 rng)))
    (if (< (modn rng 1000) (threshold profile class))
        (mv class rng)
      (mv nil rng))))
```

The loop records `:reset` when it terminates the connection, `:delay` when
it consumes a tick without sending, and `:short` when it performs the
shortened send. The deliberately wrong draw counter reports short-send hits
even for one-byte replies. The book asserts zero short landings and more
than 100 short draws over the specified 1,000-seed comparison; it asserts no
exact draw count. [^s7]

```lisp
(assert-event (equal (nth 0 (coverage 1000 1 :broad)) 0))
(assert-event (< 100 (draw-hits 1000 1)))
```

The application workload also needs opportunities for effects. R5d's device
phase supplies seeded read, write, fence, and receive trials, restarting
devices between trials. Pending storage bytes make tears possible; queued
network bytes make fragmentation possible. The fixed gate combines echo and
device landings and asserts every class landed; matched fault controls
contribute nothing to that campaign coverage. [^s28] [^s2]

The continuation records R5d as the repair for per-flight selection and
physical landing counts. Its device phase is separate evidence: a landing
there does not establish that the echo workload exercised that class.
[^s29] [^s30]

## 2.4 Give ownership an independent shadow

A successful operation result does not establish that the operation owned
its range or read initialized bytes. The OWN ownership monitor keeps
separate evidence: operation generations, output digests, input bytes, input
provenance, and snapshots for checking rejected observations. COHERENCE
names this relation Q20, the ownership shadow. [^s31] [^s32]

On input issue, OWN marks the loan's bytes unwritten. Physical byte
observations record the byte and generation; a successful read is checked
against range readability and the recorded provenance. Thus an
implementation's `:ok` answer is evidence to inspect, not the checker's
verdict. [^s33] [^s34] [^s35]

For output, OWN checks the descriptor the adapter actually consumes against
the outstanding row's operation and range identity. Identity is checked
separately from byte content, so equal bytes cannot excuse consuming the
wrong slot. Output digests provide accidental-bug evidence, not
collision-free identity. [^s36] [^s37]

A monitor also needs a connection to the real calls. The acceptance setup
installs read/write hooks around the concrete core and excludes reference
reads. Its controls mutate otherwise refused reads to return `:ok` and
require OWN to reject them; legal-read and separate-core controls check the
instrumentation itself. [^s38] [^s39]

## 2.5 Check the client's bytes, not the server's completion flag

A server can announce completion after sending the wrong bytes. The
example's verdict checker accepts the server's `done` flag or a reset; its
witness checker compares received bytes against the expected message.
Equality passes, and a shorter prefix passes only when explained by a reset.
[^s7]

```lisp
(defun first-divergence (got want i)
  (declare (xargs :guard (and (true-listp got) (true-listp want) (natp i))))
  (cond ((atom got) (if (atom want) nil (list :short-at i)))
        ((atom want) (list :extra-at i (car got)))
        ((not (equal (car got) (car want))) (list :byte-at i (car want) (car got)))
        (t (first-divergence (cdr got) (cdr want) (+ 1 i)))))

(defun check-echo (got want reset-p)
  (declare (xargs :guard (and (true-listp got) (true-listp want))))
  (let ((d (first-divergence got want 0)))
    (cond ((null d) :pass)
          ((and reset-p (eq (car d) :short-at)) :pass) ; attributed drop
          (t (list :fail d)))))

(defun check-verdict (done reset-p)
  (declare (xargs :guard t))
  (if (or done reset-p) :pass (list :fail :not-done)))
```

The mutant changes offset accumulation to `(max count off)` instead of
adding the bytes sent. This is the example's particular mutation; COHERENCE
proposes `off = count` for fn2. They illustrate the same contract failure
without being identical implementations. [^s7] [^s40]

The book asserts the unmodified server passes the witness checker over seeds
1 through 200, every example fault class lands in that sweep, and the
mutant's first witness failure is seed 8 with an extra byte at position 12:
[^s7]

```lisp
(assert-event (eq (sweep 200 12 :broad nil t) :ok))

(assert-event (let ((c (coverage 200 12 :broad)))
                (and (< 0 (nth 0 c)) (< 0 (nth 1 c)) (< 0 (nth 2 c)))))

(assert-event (equal (sweep 200 12 :broad t t)
                     '(:seed 8 (:fail (:extra-at 12 19)))))
(assert-event (equal (detections 200 12) '(24 12 12)))
(assert-event (eq (sweep 200 12 :none t t) :ok))
```

The detection tuple means 24 witness failures, 12 verdict failures, and 12
witness-only failures over those 200 seeds. With faults disabled, that same
mutant passes the specified sweep. Neither result is a universal detection
claim. [^s7]

fn2's client oracle follows the independent-message shape: the expected
stream comes from a client record, never from the core's pool. It compares
each read byte and records named drop causes; fixed acceptance rejects
unattributed drops and checks the drop total against the cause histogram.
[^s41] [^s42] [^s43]

COHERENCE's Q21 row incorrectly calls this "1,000-seed runs." The pinned
driver calls one 1,000-connection echo run with seed `20261028`.
Connections, seeds, and schedules are different coverage units. [^s44] [^s45]

## 2.6 Check work accounting and execution order separately

Internally consistent counters can all underreport the same operation. The
WORK accounting monitor first recomputes a certificate from emitted
transition records and checks record validity, caps, lost records, and
agreement with returned turn counts. It then compares charges with
independently observed outbox and posted-FIFO evidence. [^s46] [^s47] [^s48]

The FIFO snapshot is taken before the turn because harvested operation rows
may be recycled. After the turn, the monitor derives exposed input bytes,
new outbox bytes, descriptor growth, and observation consumption. Its
mutation controls keep self-reported counters consistent while the
independent evidence exposes undercharging. [^s49] [^s50] [^s51]

This is scoped accounting evidence. The cost certificate explicitly uses
declared abstract scheduler and return costs; the source says it is not a
measured CPU-cost theorem. [^s52]

The TRACE differential monitor compares the executor with a reference
implementation. Both sides can execute the same wrong handler. REVIEW-SINS
S2 identified this, and the pinned reference still shares harvest,
machine-observation, and machine-run functions. Its independent selection
machinery does not supply independent machine semantics. [^s53] [^s54] [^s55]

`fn2-check-trace-turn` imports the common adapter boundary, preserves the
reference across turns, runs both turns, and compares state differences and
returned results. That can expose scheduling disagreement. OWN and the
client oracle remain necessary because agreement between shared handlers can
hide a semantic bug. [^s56] [^s57]

## 2.7 Preserve failure all the way to the gate

Later fallout can overwrite the useful diagnosis. OWN records the first
nonzero error and leaves it intact; its final checker returns that recorded
failure before running further semantic scans. [^s58] [^s15]

```lisp
(defun fn2-own-fail (reason fn2-own)
  (declare (xargs :stobjs fn2-own :guard (unsigned-byte-p 8 reason)))
  (if (= (fn2-own-error fn2-own) 0)
      (update-fn2-own-error reason fn2-own)
    fn2-own))
```

Missing evidence needs an equally explicit result. `check.lisp` states:
"Missing evidence and unimplemented checks are never passing results." Its
dispatcher rejects bare TRACE/WORK calls with `(:fail
:checker-evidence-required)` and returns `:not-yet` for recognized
unimplemented checkers. A recognized result is not necessarily `:pass`.
[^s59] [^s60] [^s61]

fn2 violated this principle in two reviewed gates. B11 reports a
differential that classified its repaired stale-cache and live-tear
disagreements as known gaps and still returned success. H1 reports selected
surface tests that skipped while the runner returned success. Disagreement
needs failure; absent execution needs a distinct not-run outcome, not
acceptance. [^s5] [^s6]

An assertion must also reach the process status. The manual describes basic
`assert-event` assertions as "a form that evaluates to a single value that
is not a stobj"; evaluation must return a non-`nil` value or cause an error.
By default assertions are skipped during `include-book`, so including a
certified example is not a fresh campaign execution. [^s62]

T1 found drivers that printed assertion errors and nevertheless exited zero.
The pinned A4 driver checks the values returned by ACL2 loading, asserts its
campaign results, and handles a Common Lisp error by printing `ECHO
MEASUREMENT FAILED:` and exiting with code 1. [^s63] [^s1] [^s3]

## 2.8 Qualify mutations before comparing search modes

A compile error or an unreachable mutant does not demonstrate bug detection.
COHERENCE's proposed experiment freezes its mutation set before timed runs
and requires a legal witness where the original passes and the mutant
violates a named contract. The table below records that proposal. The later
E1 experiment, described after the comparison protocol, reports what was
executed. [^s64]

| Proposed mutation | Distinguishing evidence |
|---|---|
| Premature connection-row reuse | Allocation and incarnation ownership while old work remains |
| Runnable insertion at the FIFO head | Reference scheduling disagreement and admission consequence |
| Lost early borrow release | Retained ownership after both result cells are consumed |
| Premature operation recycling | Reused identity or lost evidence at the late completion |
| Wrong short-send accumulation | Incorrect client bytes or failure to complete |
| Independence declaration omitting the allocator | A legal race refuting that declaration |

The last row is a declaration defect, not a runtime defect. The unmodified
listener/reclamation race is a negative independence control: admission may
legitimately depend on whether reclamation ran first. [^s65]

"Found" means a saved, replayable legal execution violating a named
contract, with the first failing boundary identified. A failed diamond also
records the common prefix, both routes, occurrence correspondence, and first
distinguishing observation. Raw field differences are not semantic findings;
timeouts are censored measurements; duplicate detections count once per
mutant. [^s66]

The proposed generator mode separates checking local obligations at reached
states from systematically reaching states. It replays prefixes into fresh
states, enumerates finite choices at selected boundaries, and later explores
bounded prefixes over a declared domain. It keeps the concrete scheduler; it
does not arbitrarily permute internal continuations. [^s67] [^s68]

Reusing a seed after swapping events is insufficient: the next draw can
attach a fault or payload to a different operation. Paired routes need
explicit occurrence identities and correspondence. Passing bounded diamond
checks does not authorize pruning schedules in the first experiment. [^s69]

The comparison has three configurations: existing sampling, sampling through
the new explicit-choice interface with the new monitors, and bounded
enumeration through that same interface and monitors. Comparing the latter
two separates search improvements from instrumentation improvements.
Sampling and deterministic scenarios remain alongside systematic
exploration. [^s70] [^s71]

The proposal estimated **"12 engineer-days, pessimistically" for the scoped
layer-A experiment**, plus several machine-days for campaigns. It excluded
generic recursive checkpoints, partial-order reduction and a universal
declaration form. This is the planning estimate; it is not a measurement of
time spent or speed gained. [^s72]

### Measured result: E1 pass 2

**Bounded enumeration showed no search advantage over random explicit
choices on this workload.** In the main comparison, random choices found all
six qualified mutations on all three fixed seeds. Iterative deepening and
its exact-state-cache variant each found M3, M5 and M6; neither found a
qualified defect missed by random choices. The existing baseline found M2-M6
on all three seeds and had no diamond checker for M1, the defective
independence declaration. [^s73]

The frozen mutation set differs from the earlier proposal above. Its
labels mean: [^s87]

| Label | Injected defect |
|---|---|
| M1 | Declare independence by capability while omitting the shared allocator |
| M2 | Restore the old send offset after the callback updates it |
| M3 | Drop harvested-completion routing, losing its callback and wake |
| M4 | Set the send offset to the latest count instead of adding that count |
| M5 | Enqueue at the FIFO head instead of the tail, with consistent links |
| M6 | Test the wrong fault class when selecting long latency |

Those comparisons start from initialization in C1/default: the tiny
profile with one echo row and one accept credit. The original baseline
retains the broader 26-class fault environment; the explicit-choice modes
share a restricted seven-class domain. The equal-domain search comparison
is between the explicit-choice modes. [^s88] The
explicit-choice modes share a budget of 200,000 concrete/reference
transitions and 120 seconds, charging replay, checking, both diamond routes
and inline original-versus-mutant validation. Loading is excluded. Random
modes use seeds 1, 20261028 and 314159265; each enumerator uses one
deterministic order. All non-finding final campaigns exhausted their
transition budget; none hit the wall limit. These fixed-seed observations do
not estimate a performance distribution. [^s74] [^s75]

The comparison also exposed an original-system failure. The baseline's first
live phase returned `:PASS` after 200 physical accepts, 67 echoes and 133
unattributed drops. Pass 2 recorded that failure and continued; a mutation
hit had to differ from the original's first failing contract or boundary on
the same trial. A failure already present in the original was not credited
as a mutation detection. [^s76] [^s77]

Local diamond checks did produce useful positive evidence. In separate C2/data campaigns, with two echo capabilities and eight
accept credits, random exploration from initialization checked 377 legal
equal pairs, 347 with nonempty client-byte observations. These counts
include repeated instances, and the bytes can include the common prefix. A
supplied two-Send prefix also produced equal routes whose byte observations
came from the tested pair. The contract observes client bytes, closes,
terminal/drop outcomes, OWN and stop reasons through a fixed finite
continuation. This is evidence about those observations, not a proof of
independence under every future input. [^s78]

The experiment therefore separates two outcomes: local correspondence and
independence checks can be useful, while systematic enumeration may spend
its budget reaching fewer useful states. Its tiny profiles, fixed seeds and
restricted fault domain leave production workloads unmeasured. [^s79] [^s80]

## 2.9 The host remains outside this gate's conclusion

A simulated run does not establish that real devices and adapters satisfy
the simulated environment. COHERENCE calls this Q6, an X row: native
behaviors must be contained in the modeled environment. Native experiments
provide evidence about that boundary; local simulation checks do not
discharge it. [^s81] [^s82]

Nor does equality of outputs establish progress or resource bounds. fn2's
bounded-completion echo phase states a particular environment: full input,
client draining, and round-robin adapter service. Its completion bound
belongs to those premises, not to arbitrary network behavior. [^s83] [^s84]

A useful acceptance statement therefore names the workload, profile, replay
inputs, checked contract, observation boundary, landed faults, and controls.
Bounded checks can expose violations and omitted cases; they do not
establish unbounded correctness or completeness of the proposed generator
basis. [^s85] [^s30] [^s86]

[Part 3 contents](../README.md) | [Previous chapter](01-rules-as-declarations.md) | [Next chapter](03-commuting-squares.md)

[^s1]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:17 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L17).

[^s2]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:74 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L74).

[^s3]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:104 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L104).

[^s4]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:86 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L86).

[^s5]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:120 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L120).

[^s6]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:131 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L131).

[^s7]: [example: examples/assured/sim.lisp] [Source](../../examples/assured/sim.lisp).

[^s8]: [paper: tigerbeetle2026-internals-vopr.md, "Assertions and Checkers"]

[^s9]: [fn: fn2/docs/a-pool-host-sim.md:23 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L23).

[^s10]: [fn: fn2/sim/sim-state-data.lisp:15 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-state-data.lisp#L15).

[^s11]: [:doc stobj]

[^s12]: [fn: fn2/sim/sim-state.lisp:52 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-state.lisp#L52).

[^s13]: [fn: fn2/docs/a-pool-host-sim.md:25 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L25).

[^s14]: [fn: fn2/sim/check-trace.lisp:6 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-trace.lisp#L6).

[^s15]: [fn: fn2/sim/check-own.lisp:480 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L480).

[^s16]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:99 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L99).

[^s17]: [fn: fn2/sim/prng.lisp:54 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/prng.lisp#L54).

[^s18]: [fn: fn2/docs/a-pool-host-sim.md:355 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L355).

[^s19]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:5 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L5).

[^s20]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:98 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L98).

[^s21]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:51 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L51).

[^s22]: [fn: fn2/docs/a-pool-host-sim.md:465 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L465).

[^s23]: [fn: fn2/sim/sim.lisp:475 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim.lisp#L475).

[^s24]: [fn: fn2/sim/sim-adapter-base.lisp:38 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-adapter-base.lisp#L38).

[^s25]: [fn: fn2/sim/sim-state.lisp:135 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-state.lisp#L135).

[^s26]: [fn: fn2/sim/sim-adapter-base.lisp:371 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-adapter-base.lisp#L371).

[^s27]: [fn: fn2/sim/sim-adapter-base.lisp:464 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/sim-adapter-base.lisp#L464).

[^s28]: [fn: fn2/docs/a-pool-host-sim.md:430 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L430).

[^s29]: [fn: build/coordinator/fn2/lanes/a-continuation.md:161 @worktree, read 2026-10-29]

[^s30]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:83 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L83).

[^s31]: [fn: fn2/sim/check-own.lisp:8 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L8).

[^s32]: [fn: fn2/docs/design/COHERENCE.md:71 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L71).

[^s33]: [fn: fn2/sim/check-own.lisp:221 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L221).

[^s34]: [fn: fn2/sim/check-own.lisp:311 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L311).

[^s35]: [fn: fn2/sim/check-own.lisp:334 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L334).

[^s36]: [fn: fn2/sim/check-own.lisp:289 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L289).

[^s37]: [fn: fn2/sim/check-own.lisp:54 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L54).

[^s38]: [fn: fn2/docs/a-pool-host-sim.md:370 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/docs/a-pool-host-sim.md#L370).

[^s39]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:31 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L31).

[^s40]: [fn: fn2/docs/design/COHERENCE.md:848 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L848).

[^s41]: [fn: fn2/sim/echo-scenario.lisp:24 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/echo-scenario.lisp#L24).

[^s42]: [fn: fn2/sim/echo-scenario.lisp:54 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/echo-scenario.lisp#L54).

[^s43]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:91 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L91).

[^s44]: [fn: fn2/docs/design/COHERENCE.md:72 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L72).

[^s45]: [fn: fn2/tests/sim-layer-a-a4-driver.lsp:80 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/tests/sim-layer-a-a4-driver.lsp#L80).

[^s46]: [fn: fn2/sim/check-work.lisp:28 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L28).

[^s47]: [fn: fn2/sim/check-work.lisp:61 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L61).

[^s48]: [fn: fn2/sim/check-work.lisp:181 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L181).

[^s49]: [fn: fn2/sim/check-work.lisp:116 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L116).

[^s50]: [fn: fn2/sim/check-work.lisp:158 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L158).

[^s51]: [fn: fn2/sim/check-work.lisp:199 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L199).

[^s52]: [fn: fn2/sim/check-work.lisp:42 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-work.lisp#L42).

[^s53]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:87 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L87).

[^s54]: [fn: fn2/books/reference.lisp:92 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L92).

[^s55]: [fn: fn2/books/reference.lisp:142 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/books/reference.lisp#L142).

[^s56]: [fn: fn2/sim/check-trace.lisp:5 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-trace.lisp#L5).

[^s57]: [fn: fn2/docs/design/COHERENCE.md:815 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L815).

[^s58]: [fn: fn2/sim/check-own.lisp:18 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check-own.lisp#L18).

[^s59]: [fn: fn2/sim/check.lisp:2 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check.lisp#L2).

[^s60]: [fn: fn2/sim/check.lisp:14 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check.lisp#L14).

[^s61]: [fn: fn2/sim/check.lisp:64 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/check.lisp#L64).

[^s62]: [:doc assert-event]

[^s63]: [fn: fn2/docs/design/REVIEW-SINS-20261028.md:97 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/REVIEW-SINS-20261028.md#L97).

[^s64]: [fn: fn2/docs/design/COHERENCE.md:840 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L840).

[^s65]: [fn: fn2/docs/design/COHERENCE.md:842 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L842).

[^s66]: [fn: fn2/docs/design/COHERENCE.md:853 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L853).

[^s67]: [fn: fn2/docs/design/COHERENCE.md:750 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L750).

[^s68]: [fn: fn2/docs/design/COHERENCE.md:838 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L838).

[^s69]: [fn: fn2/docs/design/COHERENCE.md:752 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L752).

[^s70]: [fn: fn2/docs/design/COHERENCE.md:855 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L855).

[^s71]: [fn: fn2/docs/design/COHERENCE.md:763 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L763).

[^s72]: [fn: fn2/docs/design/COHERENCE.md:862 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L862).

[^s73]: [fn: fn2/experiments/squares/E1-RESULTS.md:14-90 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L14).

[^s74]: [fn: fn2/experiments/squares/pass2/MANIFEST.md:3-41 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/pass2/MANIFEST.md#L3).

[^s75]: [fn: fn2/experiments/squares/E1-RESULTS.md:45-50 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L45).

[^s76]: [fn: fn2/experiments/squares/E1-RESULTS.md:3-12 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L3).

[^s77]: [fn: fn2/experiments/squares/E1-RESULTS.md:19-29 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L19).

[^s78]: [fn: fn2/experiments/squares/E1-RESULTS.md:100-161 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L100).

[^s79]: [fn: fn2/experiments/squares/E1-RESULTS.md:70-98 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L70).

[^s80]: [fn: fn2/experiments/squares/E1-RESULTS.md:204-227 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/E1-RESULTS.md#L204).

[^s81]: [fn: fn2/docs/design/COHERENCE.md:57 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L57).

[^s82]: [fn: fn2/docs/design/COHERENCE.md:810 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L810).

[^s83]: [fn: fn2/sim/echo-evidence.lisp:30 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/echo-evidence.lisp#L30).

[^s84]: [fn: fn2/docs/design/COHERENCE.md:814 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L814).

[^s85]: [fn: fn2/sim/echo-scenario.lisp:450 @127f7b877] [Source](https://github.com/emberian/fn/blob/127f7b877/fn2/sim/echo-scenario.lisp#L450).

[^s86]: [fn: fn2/docs/design/COHERENCE.md:816 @66ff84f4a, read 2026-10-29] [Source](https://github.com/emberian/fn/blob/66ff84f4a/fn2/docs/design/COHERENCE.md#L816).

[^s87]: [fn: fn2/experiments/squares/mutants/README.md:23-31 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/mutants/README.md#L23).

[^s88]: [fn: fn2/experiments/squares/MANIFEST.md:7-45 @d42d18c33] [Source](https://github.com/emberian/fn/blob/d42d18c33/fn2/experiments/squares/MANIFEST.md#L7).
