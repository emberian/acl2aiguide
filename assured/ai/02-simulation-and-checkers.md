# assured/ai/02. Deterministic simulation with independent checkers as the gate

Load when building or reviewing a simulation acceptance gate.
Twin of `assured/humans/02-simulation-and-checkers.md`.
Copyable example forms below come from `examples/assured/sim.lisp`.
[example: examples/assured/sim.lisp]

## 0. Pitfalls

| symptom | cause | go to section |
| --- | --- | --- |
| Coverage passes without an exercised fault | Draws counted before effects [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:86 @worktree, read 2026-10-29] | 3 |
| Every campaign explores yesterday's schedules | Fixed seeds without exploration mode [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:99 @worktree, read 2026-10-29] | 2 |
| Illegal reads return `:ok` | Implementation verdict needs independent ownership evidence [fn: fn2/sim/check-own.lisp:334 @127f7b877] | 4 |
| Server reports completion after sending wrong bytes | Verdict checker trusts `done` [example: examples/assured/sim.lisp] | 5 |
| Work counters agree while undercharging | Shared accounting needs independent observations [fn: fn2/sim/check-work.lisp:199 @127f7b877] | 6 |
| Differential agrees on a semantic bug | Both sides execute shared handlers [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:87 @worktree, read 2026-10-29] | 6 |
| Assertion errors print; process exits zero | Failure never reaches process status [fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:97 @worktree, read 2026-10-29] | 7 |
| Mutant compiles badly or cannot execute | No legal distinguishing witness [fn: build/coordinator/fn2/COHERENCE.md:840 @worktree, read 2026-10-29] | 8 |
| Simulation passes; native behavior remains unsupported | Environment containment is a separate boundary [fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29] | 9 |

## 1. Execute the environment model itself

- Avoid a second environment model that can disagree with the simulator. Follow fn2's
  `A-SIM-IN-LOGIC`: execute the definitions later proofs will reference.
[fn: fn2/docs/a-pool-host-sim.md:23 @127f7b877]
- Keep simulator state separate from the core; make flights, devices, PRNG words,
  clocks, faults, replay metadata, and observations explicit.
[fn: fn2/sim/sim-state-data.lisp:15 @127f7b877]
- Thread stobj updates sequentially. The manual requires:
  "Updates to the object must be sequentialized."
[:doc stobj]
- Do not equate logical definitions with verified guards. At this revision,
  `fn2-check-trace-turn` and `fn2-check-own-parts` declare `:verify-guards nil`;
  the design document's blanket guard-verification claim is too broad.
[fn: fn2/docs/a-pool-host-sim.md:25 @127f7b877]
[fn: fn2/sim/check-trace.lisp:6 @127f7b877]
[fn: fn2/sim/check-own.lisp:480 @127f7b877]

## 2. Separate replay from exploration

- Fixed seeds preserve regressions but repeat schedules. Retain acceptance seeds
  and add exploration seeds; print the chosen seed before execution.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:99 @worktree, read 2026-10-29]
- Record profile, seed, observation order, fault choices, and revision. Follow the
  pinned A4 driver: print and flush mode/seed and regenerate revision metadata before scenarios.
[fn: fn2/docs/a-pool-host-sim.md:355 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:5 @127f7b877]
- Use `FN2_SWARM=1` for a fresh runtime seed or `FN2_SWARM_SEED=<decimal>` for replay.
  Treat that shorter campaign separately from fixed acceptance.
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:51 @127f7b877]
[fn: fn2/docs/a-pool-host-sim.md:465 @127f7b877]
- Read the example's replay assertion literally: it compares identical calls,
  without pinning a stored fingerprint across edits.
[example: examples/assured/sim.lisp]

```lisp
(assert-event (equal (mv-list 5 (run-seed 73 12 :broad nil))
                     (mv-list 5 (run-seed 73 12 :broad nil))))
```

## 3. Count effects after selecting applicable faults

- Reject coverage based on draws: fn2 counted selected faults before determining
  applicability. Select the flight, choose applicable classes, attempt the effect,
  then count its landing; spending fault budget is separate.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:86 @worktree, read 2026-10-29]
[fn: fn2/sim/sim.lisp:475 @127f7b877]
[fn: fn2/sim/sim-adapter-base.lisp:38 @127f7b877]
[fn: fn2/sim/sim-state.lisp:135 @127f7b877]
- Check the physical result. fn2 counts a short transfer only with `:ok` and
  a count below the requested length, after the operation returns.
[fn: fn2/sim/sim-adapter-base.lisp:371 @127f7b877]
[fn: fn2/sim/sim-adapter-base.lisp:464 @127f7b877]
- Exclude positive short sends for one-byte remainders. Copy the example's
  selection and its negative coverage control; do not invent an exact draw count.
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

(assert-event (equal (nth 0 (coverage 1000 1 :broad)) 0))
(assert-event (< 100 (draw-hits 1000 1)))
```

- Supply workload opportunities: pending storage bytes for tears, queued network
  bytes for fragmentation. Keep device-phase landings distinct from echo landings;
  matched controls contribute nothing to campaign coverage.
[fn: fn2/docs/a-pool-host-sim.md:430 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:74 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:83 @127f7b877]

## 4. Check ownership through an independent shadow

- Treat `:ok` as evidence to inspect. Mark input loans unwritten at issue; record
  physical bytes and generations; check successful reads against readability and provenance.
[fn: fn2/sim/check-own.lisp:221 @127f7b877]
[fn: fn2/sim/check-own.lisp:311 @127f7b877]
[fn: fn2/sim/check-own.lisp:334 @127f7b877]
- Check the descriptor actually consumed against outstanding operation and range
  identity. Equal bytes do not excuse a wrong slot; digests are accidental-bug evidence,
  not collision-free identity.
[fn: fn2/sim/check-own.lisp:289 @127f7b877]
[fn: fn2/sim/check-own.lisp:54 @127f7b877]
- Connect hooks to concrete core reads/writes and exclude reference reads. Require
  OWN to reject refused-read mutants returning `:ok`; retain legal-read and separate-core controls.
[fn: fn2/docs/a-pool-host-sim.md:370 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:31 @127f7b877]

## 5. Compare client bytes against independent expectations

- A completion flag can pass after wrong bytes. Compare received bytes with the
  expected message; accept a shorter prefix only with an attributed reset.
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

- Pin controls to their actual scope. The example mutates accumulation to
  `(max count off)`; over seeds 1 through 200, detections are
  `(witness-failures verdict-failures witness-only)`. Fault-free execution misses
  this mutant in the specified sweep. Copy the assertions, not a universal detection claim.
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

- Derive fn2's expected stream from the client record, never the core pool.
  Reject unattributed drops and reconcile the drop total with its cause histogram.
[fn: fn2/sim/echo-scenario.lisp:24 @127f7b877]
[fn: fn2/sim/echo-scenario.lisp:54 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:91 @127f7b877]
- Name coverage units correctly: Q21's "1,000-seed runs" is wrong.
  The pinned driver runs 1,000 echo connections with seed `20261028`.
[fn: build/coordinator/fn2/COHERENCE.md:72 @worktree, read 2026-10-29]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:80 @127f7b877]

## 6. Recompute WORK; bound TRACE's claim

- Consistent counters can undercharge together. Recompute WORK from transition
  records; check validity, caps, loss, and returned counts, then compare independent
  outbox and posted-FIFO evidence. Snapshot FIFO before rows can be recycled.
[fn: fn2/sim/check-work.lisp:28 @127f7b877]
[fn: fn2/sim/check-work.lisp:61 @127f7b877]
[fn: fn2/sim/check-work.lisp:181 @127f7b877]
[fn: fn2/sim/check-work.lisp:116 @127f7b877]
- Retain mutations with consistent self-reported counters. Describe WORK as
  accounting under declared abstract costs, not a measured CPU-cost theorem.
[fn: fn2/sim/check-work.lisp:199 @127f7b877]
[fn: fn2/sim/check-work.lisp:42 @127f7b877]
- Shared wrong handlers can make TRACE agree. The reference shares harvest,
  machine-observation, and machine-run functions. Use TRACE for scheduling disagreement;
  retain OWN and the client oracle for semantic evidence.
[fn: fn2/books/reference.lisp:92 @127f7b877]
[fn: fn2/books/reference.lisp:142 @127f7b877]
[fn: fn2/sim/check-trace.lisp:5 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:815 @worktree, read 2026-10-29]

## 7. Preserve failure through process exit

- Prevent later fallout from overwriting the diagnosis: preserve OWN's first
  nonzero error and return it before further semantic scans.
[fn: fn2/sim/check-own.lisp:18 @127f7b877]
[fn: fn2/sim/check-own.lisp:480 @127f7b877]
- Enforce: "Missing evidence and unimplemented checks are never passing results."
  Bare TRACE/WORK calls return `(:fail :checker-evidence-required)`;
  recognized unimplemented checkers return `:not-yet`. Neither is `:pass`.
[fn: fn2/sim/check.lisp:2 @127f7b877]
[fn: fn2/sim/check.lisp:14 @127f7b877]
[fn: fn2/sim/check.lisp:64 @127f7b877]
- Reject the reviewed B11/H1 patterns: known disagreements still fail;
  selected tests that skip need a distinct not-run outcome.
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:120 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/REVIEW-SINS-20261028.md:131 @worktree, read 2026-10-29]
- Use basic `assert-event` with "a form that evaluates to a single value that is not a stobj";
  it checks that evaluation "returns a non-`nil` value, causing an error otherwise."
  Default `include-book` skips assertions; inclusion is not a fresh campaign.
[:doc assert-event]
- Check ACL2 loading results and propagate failure to exit status. The pinned A4
  driver handles Common Lisp errors by printing `ECHO MEASUREMENT FAILED:` and exiting 1.
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:17 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:104 @127f7b877]

## 8. Qualify mutations before comparing search modes

- Do not count compile failures or unreachable mutants as detections. Freeze the
  mutation set before timing; require a legal witness where the original passes
  and the mutant violates a named contract. COHERENCE proposes this experiment;
  it does not report every mutation executed.
[fn: build/coordinator/fn2/COHERENCE.md:840 @worktree, read 2026-10-29]
- Count "found" only with a saved replayable legal execution and first failing
  boundary. For a failed diamond, save common prefix, both routes, occurrence
  correspondence, and first distinguishing observation. Treat timeouts as censored;
  count duplicate detections once per mutant.
[fn: build/coordinator/fn2/COHERENCE.md:853 @worktree, read 2026-10-29]
- Separate reaching states from checking local obligations. Replay prefixes into
  fresh states, enumerate finite boundary choices, and retain the concrete scheduler.
[fn: build/coordinator/fn2/COHERENCE.md:750 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:838 @worktree, read 2026-10-29]
- Do not pair reordered routes by seed alone: draws can attach to different
  operations. Supply occurrence identities and correspondence; passing bounded
  diamonds does not authorize schedule pruning in the first experiment.
[fn: build/coordinator/fn2/COHERENCE.md:752 @worktree, read 2026-10-29]
- Compare existing sampling, sampling with the new interface/monitors, and bounded
  enumeration with that same interface/monitors. Compare the latter pair to isolate
  search gains; retain sampling and deterministic scenarios.
[fn: build/coordinator/fn2/COHERENCE.md:855 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:763 @worktree, read 2026-10-29]

## 9. State the gate's boundary

- Do not infer native environment containment from simulated success.
  Q6 remains an external boundary supported by native experiments.
[fn: build/coordinator/fn2/COHERENCE.md:57 @worktree, read 2026-10-29]
[fn: build/coordinator/fn2/COHERENCE.md:810 @worktree, read 2026-10-29]
- Do not infer progress or resource bounds from equal outputs. Attach fn2's
  bounded-completion claim to full input, client draining, and round-robin adapter service.
[fn: fn2/sim/echo-evidence.lisp:30 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:814 @worktree, read 2026-10-29]
- Report workload, profile, replay inputs, contract, observation boundary, landed
  faults, and controls. Bound conclusions to the exercised domain; do not claim
  unbounded correctness or completeness of the proposed generator basis.
[fn: fn2/sim/echo-scenario.lisp:450 @127f7b877]
[fn: fn2/tests/sim-layer-a-a4-driver.lsp:83 @127f7b877]
[fn: build/coordinator/fn2/COHERENCE.md:816 @worktree, read 2026-10-29]