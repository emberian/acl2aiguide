# 2. Deterministic simulation with independent checkers as the gate

A simulator can exercise faults, print coverage, and exit successfully while
its gate has checked the wrong thing. fn2 did this: fault draws counted as
coverage before their effects occurred; a differential exempted disagreements
it had already found; selected surface tests skipped without failing the
process. These are failures of the gate, not evidence that the implementation
survived its workload.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:86 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:120 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:131 @worktree, read 2026-10-29]

The starting point is [section 5.7](../../humans/05-high-performance.md#57-tigerstyle-in-acl2):
"a seeded generator, a bounded event list, and a loop that checks the invariant
after every step and answers the first violation." This chapter develops the
gate around that loop: evidence of exercised faults, independent observations,
and controls that distinguish a correct implementation from a broken one.
[example: examples/assured/sim.lisp]

The TigerBeetle background stays in section 5.7. Its distinction between
assertions inside the implementation and additional simulator checkers is the
useful starting distinction here.
[paper: tigerbeetle2026-internals-vopr.md, "Assertions and Checkers"]

## 2.1 Put the simulated environment in the logic

A second environment model can disagree with the simulator that supplies the
test evidence. fn2's decision `A-SIM-IN-LOGIC` addresses that seam: the simulator
evaluates the environment model itself, so later proofs can refer to the same
definitions instead of introducing another model.
[fn: fn2/docs/a-pool-host-sim.md:23 @127f7b877]

The concrete arrangement is a simulator stobj separate from the core. Its
declaration contains pending-flight rows, nested network and storage stobjs,
PRNG words, clocks, fault state, replay metadata, and an observation ring.
These are explicit inputs and state for the simulated environment.
[fn: fn2/sim/sim-state-data.lisp:15 @127f7b877]

This does not put destructive assignment into the logical meaning. The manual
says, "From the logical perspective, a single-threaded object is an ordinary
ACL2 object," and gives the restriction: "Updates to the object must be
sequentialized." The simulator threads its state through its calls accordingly.
[:doc stobj]
[fn: fn2/sim/sim-state.lisp:52 @127f7b877]

The distinction between logic and verified guards matters here. The design
document says the simulator and checkers are guard-verified; that blanket claim
is too broad at this revision. `fn2-check-trace-turn` and `fn2-check-own-parts`
explicitly declare `:verify-guards nil`. Describe the implemented boundary,
rather than inheriting the document's stronger claim.
[fn: fn2/docs/a-pool-host-sim.md:25 @127f7b877]
[fn: fn2/sim/check-trace.lisp:6 @127f7b877]
[fn: fn2/sim/check-own.lisp:480 @127f7b877]

The chapter's small example uses ordinary lists and scalar arguments. It
isolates one echo connection, seeded faults, and competing checkers; it does
not reproduce fn2's nested stobj implementation.
[example: examples/assured/sim.lisp]

## 2.2 Replay needs a run description; exploration needs new seeds

A fixed acceptance seed can keep a regression reproducible while exploring
exactly yesterday's schedules. REVIEW-SINS T3 found fixed seeds throughout
fn2 and prescribed two modes: retain the acceptance seeds, and add a swarm
mode whose command-line or clock-derived seed is printed before the run.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:99 @worktree, read 2026-10-29]

fn2 uses xoshiro128** with four explicit state words. `fn2-prng-next` returns
the generated word and successor words; `fn2-sim-random` stores those successors
in the simulator. The replay description includes profile, seed, observation
order, fault choices, and revision.
[fn: fn2/sim/prng.lisp:54 @127f7b877]
[fn: fn2/sim/sim-state.lisp:52 @127f7b877]
[fn: fn2/docs/a-pool-host-sim.md:355 @127f7b877]

At the pinned revision, the A4 driver prints and flushes its mode and seed
before loading scenarios. It also regenerates the revision record before
loading them. This repairs the stale-revision failure described by T2.
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:5 @127f7b877]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:98 @worktree, read 2026-10-29]

The fixed branch runs the pool campaigns and the echo workload with their
specified seeds. `FN2_SWARM=1` selects a fresh runtime seed;
`FN2_SWARM_SEED=<decimal>` supplies one for replay. The swarm branch is a
shorter campaign, not the fixed acceptance branch under another label.
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:51 @127f7b877]
[fn: fn2/docs/a-pool-host-sim.md:465 @127f7b877]

The example uses xorshift32, not fn2's xoshiro128**. Its replay assertion is
exactly this:
[example: examples/assured/sim.lisp]

```lisp
(assert-event (equal (mv-list 5 (run-seed 73 12 :broad nil))
                     (mv-list 5 (run-seed 73 12 :broad nil))))
```

That compares identical calls; it does not pin a stored fingerprint across
edits. The later mutant assertion pins a specific failure value. Do not turn
the example's replay comment into a stronger regression claim than its forms.
[example: examples/assured/sim.lisp]

## 2.3 Count the fault's effect

A selected fault may do nothing. REVIEW-SINS S1 found that fn2 incremented
coverage when drawing a class, before determining whether it applied to the
next flight. A storage read error selected during a receive could therefore
help satisfy the coverage assertion without exercising that error.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:86 @worktree, read 2026-10-29]

R5d changed the order: select the flight, choose from classes applicable to its
kind and stage, attempt the effect, and count the landing at the effect.
`fn2-sim-advance` selects the flight before calling
`fn2-sim-choose-flight-fault`; selection spends fault budget without incrementing
the landing counter.
[fn: fn2/sim/sim.lisp:475 @127f7b877]
[fn: fn2/sim/sim-adapter-base.lisp:38 @127f7b877]
[fn: fn2/sim/sim-state.lisp:135 @127f7b877]

Applicability is not success. The physical landing predicate checks the
result: a short transfer requires `:ok` and a count below the requested
length; a lying fence requires a dirty fence and the lying behavior.
The counter is updated after the physical operation returns.
[fn: fn2/sim/sim-adapter-base.lisp:371 @127f7b877]
[fn: fn2/sim/sim-adapter-base.lisp:464 @127f7b877]

In the example, a one-byte remainder cannot have a positive short send.
The candidate list excludes that class before drawing:
[example: examples/assured/sim.lisp]

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

The loop records `:reset` when it terminates the connection, `:delay` when it
consumes a tick without sending, and `:short` when it performs the shortened
send. The deliberately wrong draw counter reports short-send hits even for
one-byte replies. The book asserts zero short landings and more than 100
short draws over the specified 1,000-seed comparison; it asserts no exact
draw count.
[example: examples/assured/sim.lisp]

```lisp
(assert-event (equal (nth 0 (coverage 1000 1 :broad)) 0))
(assert-event (< 100 (draw-hits 1000 1)))
```

The application workload also needs opportunities for effects. R5d's device
phase supplies seeded read, write, fence, and receive trials, restarting devices
between trials. Pending storage bytes make tears possible; queued network
bytes make fragmentation possible. The fixed gate combines echo and device
landings and asserts every class landed; matched fault controls contribute
nothing to that campaign coverage.
[fn: fn2/docs/a-pool-host-sim.md:430 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:74 @127f7b877]

The continuation records R5d as the repair for per-flight selection and
physical landing counts. Its device phase is separate evidence: a landing
there does not establish that the echo workload exercised that class.
[fn: build/coordinator/fn2/lanes/a-continuation.md:161 @worktree, read 2026-10-29]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:83 @127f7b877]

## 2.4 Give ownership an independent shadow

A successful operation result does not establish that the operation owned its
range or read initialized bytes. OWN keeps separate evidence: operation
generations, output digests, input bytes, input provenance, and snapshots for
checking rejected observations. COHERENCE names this relation Q20, the
ownership shadow.
[fn: fn2/sim/check-own.lisp:8 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:71 @worktree, read 2026-10-29]

On input issue, OWN marks the loan's bytes unwritten. Physical byte observations
record the byte and generation; a successful read is checked against range
readability and the recorded provenance. Thus an implementation's `:ok`
answer is evidence to inspect, not the checker's verdict.
[fn: fn2/sim/check-own.lisp:221 @127f7b877]
[fn: fn2/sim/check-own.lisp:311 @127f7b877]
[fn: fn2/sim/check-own.lisp:334 @127f7b877]

For output, OWN checks the descriptor the adapter actually consumes against
the outstanding row's operation and range identity. Identity is checked
separately from byte content, so equal bytes cannot excuse consuming the
wrong slot. Output digests provide accidental-bug evidence, not
collision-free identity.
[fn: fn2/sim/check-own.lisp:289 @127f7b877]
[fn: fn2/sim/check-own.lisp:54 @127f7b877]

A monitor also needs a connection to the real calls. The acceptance setup
installs read/write hooks around the concrete core and excludes reference
reads. Its controls mutate otherwise refused reads to return `:ok` and require
OWN to reject them; legal-read and separate-core controls check the
instrumentation itself.
[fn: fn2/docs/a-pool-host-sim.md:370 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:31 @127f7b877]

## 2.5 Check the client's bytes, not the server's completion flag

A server can announce completion after sending the wrong bytes. The example's
verdict checker accepts the server's `done` flag or a reset; its witness checker
compares received bytes against the expected message. Equality passes, and a
shorter prefix passes only when explained by a reset.
[example: examples/assured/sim.lisp]

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

The mutant changes offset accumulation to `(max count off)` instead of adding
the bytes sent. This is the example's particular mutation; COHERENCE proposes
`off = count` for fn2. They illustrate the same contract failure without being
identical implementations.
[example: examples/assured/sim.lisp]
[fn: build/coordinator/fn2/COHERENCE.md:848 @worktree, read 2026-10-29]

The book asserts the unmodified server passes the witness checker over seeds
1 through 200, every example fault class lands in that sweep, and the mutant's
first witness failure is seed 8 with an extra byte at position 12:
[example: examples/assured/sim.lisp]

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
claim.
[example: examples/assured/sim.lisp]

fn2's client oracle follows the independent-message shape: the expected stream
comes from a client record, never from the core's pool. It compares each read
byte and records named drop causes; fixed acceptance rejects unattributed
drops and checks the drop total against the cause histogram.
[fn: fn2/sim/echo-scenario.lisp:24 @127f7b877]
[fn: fn2/sim/echo-scenario.lisp:54 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:91 @127f7b877]

COHERENCE's Q21 row incorrectly calls this "1,000-seed runs." The pinned
driver calls one 1,000-connection echo run with seed `20261028`. Connections,
seeds, and schedules are different coverage units.
[fn: build/coordinator/fn2/COHERENCE.md:72 @worktree, read 2026-10-29]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:80 @127f7b877]

## 2.6 Recompute work; state what TRACE shares

Internally consistent counters can all underreport the same operation. WORK
first recomputes a certificate from emitted transition records and checks
record validity, caps, lost records, and agreement with returned turn counts.
It then compares charges with independently observed outbox and posted-FIFO
evidence.
[fn: fn2/sim/check-work.lisp:28 @127f7b877]
[fn: fn2/sim/check-work.lisp:61 @127f7b877]
[fn: fn2/sim/check-work.lisp:181 @127f7b877]

The FIFO snapshot is taken before the turn because harvested operation rows
may be recycled. After the turn, the monitor derives exposed input bytes,
new outbox bytes, descriptor growth, and observation consumption. Its mutation
controls keep self-reported counters consistent while the independent
evidence exposes undercharging.
[fn: fn2/sim/check-work.lisp:116 @127f7b877]
[fn: fn2/sim/check-work.lisp:158 @127f7b877]
[fn: fn2/sim/check-work.lisp:199 @127f7b877]

This is scoped accounting evidence. The cost certificate explicitly uses
declared abstract scheduler and return costs; the source says it is not a
measured CPU-cost theorem.
[fn: fn2/sim/check-work.lisp:42 @127f7b877]

TRACE has a different limitation: both sides can execute the same wrong
handler. REVIEW-SINS S2 identified this, and the pinned reference still shares
harvest, machine-observation, and machine-run functions. Its independent
selection machinery does not supply independent machine semantics.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29]
[fn: fn2/books/reference.lisp:92 @127f7b877]
[fn: fn2/books/reference.lisp:142 @127f7b877]

`fn2-check-trace-turn` imports the common adapter boundary, preserves the
reference across turns, runs both turns, and compares state differences and
returned results. That can expose scheduling disagreement. OWN and the client
oracle remain necessary because agreement between shared handlers can hide
a semantic bug.
[fn: fn2/sim/check-trace.lisp:5 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:815 @worktree, read 2026-10-29]

## 2.7 Preserve failure all the way to the gate

Later fallout can overwrite the useful diagnosis. OWN records the first
nonzero error and leaves it intact; its final checker returns that recorded
failure before running further semantic scans.
[fn: fn2/sim/check-own.lisp:18 @127f7b877]
[fn: fn2/sim/check-own.lisp:480 @127f7b877]

```lisp
(defun fn2-own-fail (reason fn2-own)
  (declare (xargs :stobjs fn2-own :guard (unsigned-byte-p 8 reason)))
  (if (= (fn2-own-error fn2-own) 0)
      (update-fn2-own-error reason fn2-own)
    fn2-own))
```

Missing evidence needs an equally explicit result. `check.lisp` states:
"Missing evidence and unimplemented checks are never passing results."
Its dispatcher rejects bare TRACE/WORK calls with
`(:fail :checker-evidence-required)` and returns `:not-yet` for recognized
unimplemented checkers. A recognized result is not necessarily `:pass`.
[fn: fn2/sim/check.lisp:2 @127f7b877]
[fn: fn2/sim/check.lisp:14 @127f7b877]
[fn: fn2/sim/check.lisp:64 @127f7b877]

fn2 violated this principle in two reviewed gates. B11 reports a differential
that classified its repaired stale-cache and live-tear disagreements as known
gaps and still returned success. H1 reports selected surface tests that skipped
while the runner returned success. Disagreement needs failure; absent execution
needs a distinct not-run outcome, not acceptance.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:120 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:131 @worktree, read 2026-10-29]

An assertion must also reach the process status. The manual describes basic
`assert-event` assertions as "a form that evaluates to a single value that is
not a stobj"; evaluation must return a non-`nil` value or cause an error.
By default assertions are skipped during `include-book`, so including a
certified example is not a fresh campaign execution.
[:doc assert-event]

T1 found drivers that printed assertion errors and nevertheless exited zero.
The pinned A4 driver checks the values returned by ACL2 loading, asserts its
campaign results, and handles a Common Lisp error by printing
`ECHO MEASUREMENT FAILED:` and exiting with code 1.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:97 @worktree, read 2026-10-29]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:17 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:104 @127f7b877]

## 2.8 Qualify mutations before comparing search modes

A compile error or an unreachable mutant does not demonstrate bug detection.
COHERENCE's proposed experiment freezes its mutation set before timed runs
and requires a legal witness where the original passes and the mutant violates
a named contract. These are proposed fn2 mutations to qualify, not a report
that every mutation has already been executed.
[fn: build/coordinator/fn2/COHERENCE.md:840 @worktree, read 2026-10-29]

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
legitimately depend on whether reclamation ran first.
[fn: build/coordinator/fn2/COHERENCE.md:842 @worktree, read 2026-10-29]

"Found" means a saved, replayable legal execution violating a named contract,
with the first failing boundary identified. A failed diamond also records the
common prefix, both routes, occurrence correspondence, and first distinguishing
observation. Raw field differences are not semantic findings; timeouts are
censored measurements; duplicate detections count once per mutant.
[fn: build/coordinator/fn2/COHERENCE.md:853 @worktree, read 2026-10-29]

The proposed generator mode separates checking local obligations at reached
states from systematically reaching states. It replays prefixes into fresh
states, enumerates finite choices at selected boundaries, and later explores
bounded prefixes over a declared domain. It keeps the concrete scheduler;
it does not arbitrarily permute internal continuations.
[fn: build/coordinator/fn2/COHERENCE.md:750 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:838 @worktree, read 2026-10-29]

Reusing a seed after swapping events is insufficient: the next draw can
attach a fault or payload to a different operation. Paired routes need explicit
occurrence identities and correspondence. Passing bounded diamond checks
does not authorize pruning schedules in the first experiment.
[fn: build/coordinator/fn2/COHERENCE.md:752 @worktree, read 2026-10-29]

The comparison has three configurations: existing sampling, sampling through
the new explicit-choice interface with the new monitors, and bounded
enumeration through that same interface and monitors. Comparing the latter
two separates search improvements from instrumentation improvements. Sampling
and deterministic scenarios remain alongside systematic exploration.
[fn: build/coordinator/fn2/COHERENCE.md:855 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:763 @worktree, read 2026-10-29]

The estimate is **"12 engineer-days, pessimistically" for the scoped layer-A
experiment**, plus several machine-days for campaigns; it excludes generic
recursive checkpoints, partial-order reduction, and a universal declaration
form. This is an estimate for a proposed experiment, not a measured speedup.
[fn: build/coordinator/fn2/COHERENCE.md:862 @worktree, read 2026-10-29]

## 2.9 The host remains outside this gate's conclusion

A simulated run does not establish that real devices and adapters satisfy the
simulated environment. COHERENCE calls this Q6, an X row: native behaviors must
be contained in the modeled environment. Native experiments provide evidence
about that boundary; local simulation checks do not discharge it.
[fn: build/coordinator/fn2/COHERENCE.md:57 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29]

Nor does equality of outputs establish progress or resource bounds. fn2's
bounded-completion echo phase states a particular environment: full input,
client draining, and round-robin adapter service. Its completion bound belongs
to those premises, not to arbitrary network behavior.
[fn: fn2/sim/echo-evidence.lisp:30 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:814 @worktree, read 2026-10-29]

A useful acceptance statement therefore names the workload, profile, replay
inputs, checked contract, observation boundary, landed faults, and controls.
Bounded checks can expose violations and omitted cases; they do not establish
unbounded correctness or completeness of the proposed generator basis.
[fn: fn2/sim/echo-scenario.lisp:450 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:83 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:816 @worktree, read 2026-10-29]
