# ai/06. Process, and running ACL2 from an agent

Load whole before doing ACL2 work as an agent. The terse twin of
`humans/06-process.md`, plus the operating rules for one agent driving ACL2:
one session, batched forms, limits on every form, certify before reporting,
background anything long. See `fn-lessons/19-foreground-waits-and-censuses.md`
and `fn-lessons/13-certificate-cache.md` for the wounds. Citations as in
`ai/03-prover.md`; fn coordinator files are cited `@worktree` (read
2026-10-28). "The laptop" is ACL2 8.7, SBCL 2.6.8,
`~/tools/acl2-fn/acl2-literal-4g-tls64k`.

## 0. Pitfalls

| symptom | cause | go to |
| --- | --- | --- |
| a proved keystone is vacuous or about the wrong function | no statement-first witnesses | 1 |
| a `must-fail` offered as the counterexample | it is only a failed search | 2 |
| a representation chosen to make a proof easy, then kept | proving before the behaviour is right | 3 |
| the apparatus outgrows the program | checkers and registers for what the logic or world can say | 4 |
| two configurations compared on step-limited aborts | an abort measures nothing | 5 |
| each edit costs a closure certification | certification used as the edit loop | 7 |
| "The name F is in use as a function ... The redefinition feature is currently off" | the session already has the old definition | 7.4 |
| `FAILED` after exactly your `timeout` | your limit, not ACL2's verdict | 7.5 |
| exit status 0 from a run that failed | ACL2 reads to EOF and quits 0 | 7.2, 8 |
| a `.cert` beside a changed book taken as green | stale certificate | 8 |
| half your wall clock in `until ...; sleep` loops | foreground waiting | 9 |
| a lane spends context answering "status?" | censuses instead of event reports | 10 |

## 1. Statement first

Pitfall: a theorem true, proved and useless (vacuous premise, wrong subject, not
the property needed); the prover proves what it is given. fn's coordinator
approved three statement packets that held 3, 2 and 5 false statements
[fn: build/coordinator/PROCESS-AUDIT-20261009.md:60,78 @worktree]. Rule: every
keystone enters with a satisfiable-premise witness and teeth before proof work;
"approved to prove" only after an ACL2 counterexample search and its witnesses
[fn: build/coordinator/PROCESS-AUDIT-20261009.md:79 @worktree]. The subject is
"the function the host calls, or a named theorem equates them"
[fn: AGENTS.md:24-25 @3bbfc4dca]; invariants need "meaningful initial states and
reachable examples" [fn: docs/proofs.md:65-69 @3bbfc4dca]. Non-vacuity is owed
at the top theorems [fn: OWED.md:13-20 @3bbfc4dca].

Shape: the claim as two macros, so the witnesses evaluate the term the theorem
states; book order statement, witness, teeth, refusal, proof
[example: examples/process/statement-first.lisp]:

```lisp
(defun enqueue (x q cap)
  (declare (xargs :guard (and (true-listp q) (natp cap))))
  (if (< (len q) cap)
      (mv :ok (append q (list x)))
    (mv :full q)))

(defmacro enqueue-claim-hyps (q cap)
  `(and (true-listp ,q)          ; H1: a queue
        (natp ,cap)              ; H2: a capacity
        (<= (len ,q) ,cap)))     ; H3: the queue is within it already

(defmacro enqueue-claim-concl (x q cap)
  `(<= (len (mv-nth 1 (mv-list 2 (enqueue ,x ,q ,cap)))) ,cap))

(assert-event (let ((x 'c) (q '(a b)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (equal (car (mv-list 2 (enqueue x q cap))) :ok)
                     (enqueue-claim-concl x q cap))))
```

`mv-list` is required: `(mv-nth 1 (enqueue ...))` in an `assert-event` is
refused ("It is illegal to invoke ENQUEUE") [example: examples/process/statement-first.lisp].

## 2. Teeth

Pitfalls:

- "Never a general negated `must-fail`: it proves that the prover could not
  find a proof, which is not a counterexample, and it loops when the negation
  is unprovable rather than false" [fn: docs/proof-style.md:381-383 @3bbfc4dca].
  A `must-fail` counts only beside a concrete violating value.
- A mutant only an unreachable state reveals proves nothing
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:17 @worktree].
- Teeth run at certification, not on include: `assert-event` is skipped when
  proofs are skipped unless `:on-skip-proofs t` [:doc assert-event].

Rule: "a reachable non-degenerate witness and one concrete violating value per
hypothesis, each an `assert-event` on the negated conclusion"; a hypothesis
with no violating value is deleted or recorded; an unevaluable one gets a
labelled `must-fail` [fn: docs/proof-style.md:349-394 @3bbfc4dca]. Shape
[example: examples/process/statement-first.lisp]:

```lisp
; Remove H3: a queue already over its capacity stays over it.
(assert-event (let ((x 'z) (q '(a b c d e)) (cap 3))
                (and (true-listp q) (natp cap)          ; H1, H2 hold
                     (not (<= (len q) cap))             ; H3 fails
                     (not (enqueue-claim-concl x q cap)))))

; logical: cap = -1 violates enqueue's guard (natp cap).
(assert-event (with-guard-checking
               :none
               (let ((x 'z) (q nil) (cap -1))
                 (and (true-listp q)                    ; H1 holds
                      (not (natp cap))                  ; H2 fails
                      (not (enqueue-claim-concl x q cap))))))

; teeth: prover-refusal  The same mutant, as a theorem the prover refuses.
(must-fail
 (defthm enqueue-mutant-strict
   (implies (enqueue-claim-hyps q cap)
            (< (len (mv-nth 1 (enqueue x q cap))) cap))))

(defthm enqueue-stays-within-capacity
  (implies (enqueue-claim-hyps q cap)
           (enqueue-claim-concl x q cap)))
```

A violating value outside the guard domain runs under `with-guard-checking
:none` and its comment says `logical` (fn's `:logical "why"`, counted as debt)
[fn: docs/proof-style.md:352-358 @3bbfc4dca]. Bind teeth to the stored formula
or they drift [fn: books/defkeystone.lisp:48-53 @3bbfc4dca]. More shapes:
`ai/04-modelling.md` section 16.

## 3. What to prove early, what late

Statement first; proof of anything whose subject is not yet the shipped
function, late. ember: "get the software like .... working. and then also
correct/proven ;) :D sometimes we shouldn't do those at the same time !!!!"
[fn: build/coordinator/EMBER.md:540-549 @worktree]; competing representations
"were originally designed to make the refinement proofs easier"
[fn: build/coordinator/EMBER.md:267-271 @worktree]. Choose the representation
for the machine; adapt the proof through an abstraction (`mbe`, abstract
stobj, functional instance). "The program used by the host must be these
definitions or a justified refinement" [fn: docs/proofs.md:59-61 @3bbfc4dca].
Generalize generators from two working instances
[fn: build/coordinator/RUNTIME-MODEL-DRAFT-20261009.md:39 @worktree].

## 4. Evidence, ledgers, checkers

- Kinds of evidence are separate: admission, guard verification, theorem,
  certification, platform tests; disclose trusted facilities
  [fn: docs/proofs.md:92-95 @3bbfc4dca].
- Read status from the world, not from source:
  `(assert-event (eq (symbol-class 'count-tag-st (w state)) :common-lisp-compliant))`
  [example: examples/performance/mbe-fixnum-loop.lisp]; "Only `verified` is
  an observation" [fn: docs/proofs.md:186-197 @3bbfc4dca].
- No typed counts in prose: "a number that is typed is a number that drifts"
  [fn: docs/proofs.md:36-39 @3bbfc4dca].
- Green means certified at the current bytes: "A commit message, a proposed
  theorem or passing tests are not certification" [fn: AGENTS.md:36-37 @3bbfc4dca].
- Delete a checker whose rule the logic can state, a register that restates the
  world, and any document whose checker is gone without saying so. fn: "The
  checkers are a third again the size of the host they check"
  [fn: build/coordinator/ANATOMY-20261009.md:28 @worktree]; the coordinator's
  own confession, "every gate I rule into existence is Python with a unit test"
  [fn: build/coordinator/AUDIT-TWO-WEEKS-20261013.md:50 @worktree].

## 5. Sizing proofs

- Read `Time:` first: `prove: 0.02, ... other: 2386.24` is "a **theory change,
  not a hint**" [fn: docs/proof-style.md:591-605 @3bbfc4dca]
  (`ai/03-prover.md` section 2.6).
- Profile before hinting (`accumulated-persistence`)
  [fn: docs/proof-style.md:561-582 @3bbfc4dca].
- A step-limited abort says nothing; "a `yes` is evidence while a `no` is not";
  compare without a limit under a wall-clock `timeout`
  [fn: docs/proof-style.md:650-667 @3bbfc4dca]. Shape
  [example: examples/process/step-limit-probe.lisp]:

  ```lisp
  (must-fail
   (with-prover-step-limit 20
     (defthm app-assoc-probe
       (equal (app (app x y) z) (app x (app y z))))))

  (with-prover-time-limit 30
    (defthm app-assoc
      (equal (app (app x y) z) (app x (app y z)))))
  ```

  The refusal prints `The prover step-limit, which is 20 in the current
  context, has been exceeded`, `Prover steps counted: More than 20`, `No
  checkpoints to print`; unlimited it proves in 435 steps
  [measured: the same form outside `must-fail`, laptop REPL; the 435 is in the
  book's `.cert.out`].
- Ratchet steps, not seconds: same count "on any box at any load"; a book fails
  10 % over its baseline; the baseline only shrinks; "never raise a timeout or
  weaken a statement" [fn: docs/proofs.md:114-167 @3bbfc4dca].
- Split a book over 800 lines at its seam; splitting must reduce total or
  critical-path work [fn: docs/proof-style.md:411-415 @3bbfc4dca],
  [fn: docs/proofs.md:169-171 @3bbfc4dca].
- Prefer a new book low in the include graph: changing a book recertifies
  everything above it [fn: docs/proof-style.md:445-455 @3bbfc4dca].
- Never include a book for one lemma non-locally (six minutes became an 1800 s
  timeout) [fn: docs/proofs.md:262-265 @3bbfc4dca].
- One world, no twins: "grow the generator, never hand-write a twin"
  [fn: AGENTS.md:20-21 @3bbfc4dca]; copying 361 shared books to dodge a
  `local` problem was ruled "delete the forest"
  [fn: build/coordinator/RULINGS.md:61 @worktree].

## 6. Skipped proofs, honestly

`skip-proofs` is "a quick way to introduce unsoundness"; a script with it is
"work-in-progress, not ... a completed proof"; a book needs `:skip-proofs-okp t`
and includes with a warning, an error under `:skip-proofs-okp nil`
[:doc skip-proofs]. fn forbids `skip-proofs`, `defaxiom`, `defttag`,
`set-raw-mode`, `include-raw` by scan [fn: tools/certify_books.py:108 @3bbfc4dca]
and files an unproved theorem as a `proof-owed` ledger row, never an assumed
event [fn: build/coordinator/lanedumps/actors.md:32 @worktree]. Skipped proofs
are for triage only (provisional certification, `ai/03-prover.md` section 9.3):
"**A triage run is evidence of nothing but its list of reds.**"
[fn: docs/proofs.md:588 @3bbfc4dca].

## 7. Running ACL2 from an agent

### 7.1 One live session, not certification, as the edit loop

"The wrong loop for proof work is `certify-book`: twenty minutes a closure on
the farm, and a red at the bottom hides everything above it"
[fn: tools/proof_repl.py:4-7 @3bbfc4dca]. The loop: one ACL2 with the book's
certified dependencies included, the book's events loaded up to the one that
fails, each attempt costing only its own proof
[fn: tools/proof_repl.py:7-10 @3bbfc4dca]. fn's `proof_repl.py` (`start NAME
BOOK --upto EVENT`, `send`, `send-range`, `probe`) answers with key checkpoints
and ACL2's own `Time:` and step count, wraps each event in
`with-prover-time-limit`, and idles out after 20 minutes
[fn: docs/proofs.md:489-552 @3bbfc4dca]. "A form ACL2 admits there is not a
certificate; the event goes into the book and the book certifies"
[fn: docs/proofs.md:505-506 @3bbfc4dca].

Rule, from ember: the failure mode is "iterating one statement at a time instead
of iterating across the whole system and using mental simulations and reasoning
in our mind to metarationally develop without wasteful rerun loops of bullshit
slow things" [fn: build/coordinator/EMBER.md:392 @worktree]. So: read the
definitions and the checkpoint, predict what each candidate lemma or hint does,
write all of them, and send them in one batch. Rerun only after a change you
expect to change the outcome.

### 7.2 The driver-file batch

Plain ACL2's equivalent of a live session: one file of forms, piped once,
output read once. The driver's form (gag mode, a certified include, a batched
`ld` with `:ld-error-action :continue`, history and break-rewrite commands) is
`ai/01-form-shapes.md` section 16; run it as

```
cd <repo>/examples && \
  timeout 60 ~/tools/acl2-fn/acl2-literal-4g-tls64k < driver.lsp > driver.out 2>&1
```

A minimal driver here (`(set-gag-mode :goals)`, `(include-book
"prover/induction-lemma-first")`, then two events each under
`(with-prover-time-limit 30 ...)`) took 0.20 s real, 0.04 s of it the
certified include; the first event proved in 184 steps; the second, `(thm
(implies (natp i) (equal (len (drop i x)) (- (len x) i))))`, printed `FAILED`
with the checkpoint `(IMPLIES (AND (NOT (CONSP X)) (<= 0 I)) (ZP I))`, false at
`i = 1`, so the conjecture is false (`ai/03-prover.md` 2.3); and the process
exited 0 [measured: that driver, from `examples/`, laptop, 2026-10-28]. Rules:

- Include certified books for everything below the form under work; do not
  re-prove the closure. `include-book` paths resolve against the directory
  ACL2 starts in [measured: same run].
- Batch every form you can predict; one run per coherent change.
- The exit status says nothing: ACL2 reads to EOF, prints `Bye.` and exits 0
  after failed events [measured: same run]. Search the output for `FAILED`,
  `ACL2 Error`, `Key checkpoint`, `Summary`.
- Set `ACL2_CUSTOMIZATION=NONE` and `ACL2_BOOK_HASH_ALISTP=NIL` "so an `ld`
  session iterates against the world certification will see"; `cert.pl` sets
  the customization to `NONE` itself [fn: docs/proofs.md:640-641 @3bbfc4dca],
  [:doc acl2-customization].
- A wrapper with its own timeout and an exit code (fn: `tools/acl2 --timeout
  240 < driver.lsp`, exit 124) makes the time bound mechanical
  [fn: docs/proofs.md:643-645 @3bbfc4dca]; scratch drivers that bypass the
  machine's slot pool overload it (six ACL2s on a four-slot laptop)
  [fn: docs/proofs.md:636-637 @3bbfc4dca]. Here the pool is
  `examples/certify.sh`'s lock for certifications: one at a time.

### 7.3 Output and limits

- `(set-gag-mode :goals)` (the default) prints goal names and key checkpoints;
  `:pso` after the fact; `(set-gag-mode nil)` only when you need the whole
  narration [:doc set-gag-mode], [:doc pso].
- Every sent event under `with-prover-time-limit`: runtime by default; aborts
  print `ACL2 Error [Time-limit] ... Out of time in ...`
  [:doc with-prover-time-limit] [measured: `(with-prover-time-limit 1/1000
  (defthm app-assoc-tl ...))`, laptop REPL]. A time limit is for the session;
  inside a book prefer step limits [:doc best-practices].
- A step limit answers only "closes within n?" (section 5).

### 7.4 The REPL does not take edits

A changed `defun` is refused ("The redefinition feature is currently off"), an
identical one is redundant [measured: two `defun f` forms at the laptop REPL];
`ai/01-form-shapes.md` section 16 has the transcript. Rules: after editing a
book or test, restart the session
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:24 @worktree], or
`:ubt` back past the event [:doc ubt]. Do not turn redefinition on: "ACL2 is
liable to be made unsafe or unsound" [:doc ld-redefinition-action]. A trial
lemma left in the session changes the next attempt's step count (161 instead
of 7,313); undo it [fn: docs/proofs.md:544-549 @3bbfc4dca].

### 7.5 Timeouts are yours

A form cut by the shell's `timeout` printed `Time: 119.49 seconds (prove:
0.00, print: 0.00, other: 119.49)`, "No checkpoints to print" and `FAILED`; at
`timeout 240` it was still running [measured: the `bench-stobj` draft over
the 1,000,000-word `vec` of examples/performance/time-list-vs-stobj.lisp, laptop
REPL under `timeout 120` and again under `timeout 240`]. A
FAILED at your own limit is your limit, not a verdict.

### 7.6 Stobj and attachment traps at the REPL

`with-local-stobj` returns the other values, never the stobj; a stobj argument
is a variable, bind with `let` first; `loop$` bodies need badged functions
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:26 @worktree]
(`ai/04-modelling.md` section 6). A compiled function running
`with-local-stobj` of an attachable stobj loaded after its attach book makes
certification illegal and the REPL does not show it: evaluate `(@
illegal-to-certify-message)` at the end [cv: ac5fb887#20].

## 8. Certify before reporting; what a certificate covers

- Certify the books you changed, and their test books, yourself, before you
  report: `examples/certify.sh <dir>/<book>.lisp` here (cert.pl under the lock),
  and read the `Built ... .cert` line. fn's rule: "a lane certifies what it
  changed and its test books on the farm before it reports"; behind it, a `dev`
  red for a day in four books "each committed by a lane that never certified it"
  [fn: docs/proofs.md:449-453,469-471 @3bbfc4dca].
- A certificate covers the book and its whole include closure: "the key is the
  closure" [fn: docs/proofs.md:308-312 @3bbfc4dca]. Set
  `ACL2_BOOK_HASH_ALISTP=NIL` before ACL2 starts so the book-hash is a checksum,
  not size and write-date [:doc book-hash]; then "a `.cert`/`.port` pair is
  valid in any worktree and on any host whose book content matches"
  [fn: docs/proofs.md:295-298 @3bbfc4dca].
- "a `.cert` lying beside a book proves nothing, since after a merge it can be
  the previous source's certificate" [fn: docs/proofs.md:299-302 @3bbfc4dca].
- The `.fasl` travels with the pair and must not be older than the `.cert`,
  or the book loads uncompiled [fn: docs/proofs.md:351-355 @3bbfc4dca],
  [:doc include-book].
- A failed certification can exit 0 ("the certify driver ends in `(quit)`");
  read the verdict, not the exit code [fn: docs/proofs.md:607-611 @3bbfc4dca].
- `start --certify-missing` in fn's tool certified only dependencies, never the
  book itself [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:22 @worktree].
- A lock released by a shell `trap` must not follow an `exec`: this guide's
  `certify.sh` once `exec`ed `cert.pl` and leaked its lock to every later run
  [measured: `examples/.cert.lock` present with no `cert.pl` running, before
  `ce2c34b`; laptop].

## 9. Long work: background, PID file, no foreground waits

- Anything that may run past the tool call's limit (budget 100 s against a
  120 s limit) runs in the background: "`send-file` of a long run exceeds a 120
  s tool timeout: run it in the background"
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:25 @worktree].
- Never wait in the foreground: two integrator seats "spent 5.4 h of 10.4 h in
  77 calls over 60 s (most of them `until grep ... ; do sleep 15` loops)"; seats
  using a background job and a monitor spent 0.04 h and 0 h
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:66 @worktree]. Forest-wide:
  "Foreground waits 7.3 h of 22.9 h seat time (32%)"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:11 @worktree]. Wait on one
  completion line, in the background, and keep working.
- Every background process writes a PID file; stop it by that PID only, never
  by pattern; "Never a whole-disk `find` and never a background command without
  a PID file" [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:27 @worktree].
  The lane that broke this left a stray `find` for the owner to stop
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:3 @worktree].
- Shape, for a certification that may be long:

  ```
  cd <repo> && \
    nohup timeout 3600 examples/certify.sh <dir>/<book>.lisp > SCRATCH/cert.log 2>&1 < /dev/null &
  echo $! > SCRATCH/cert.pid
  ```

  (fn's form: `nohup timeout 3600 ... > LOG 2>&1 < /dev/null & echo $! > PID`
  [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:22 @worktree]);
  check liveness with `kill -0 $(cat SCRATCH/cert.pid)`, read the log once.

## 10. Working in a fleet

- Report on events, never on a schedule: fn's audit counted "49 messages to the
  coordinator: 28 READY, 7 BLOCKED, 5 DECISION, 4 RED, 5 park notices ... 0
  status or FYI" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:13 @worktree].
  Never run or answer a status census; the event stream carries status.
- Resume the agent that holds the context; a successor starts from the
  predecessor's own continuation file, never a summary: "5 successions ...,
  each from the predecessor's own continuation file ... no lost thread found"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:12 @worktree].
- Park before the ceiling: "a builder writes its continuation and parks at
  400k, not 790k" [fn: build/coordinator/PROCESS-AUDIT-20261009.md:71 @worktree].
- Read the usage gauge before long work; at 70 % finish the item in hand and
  park [fn: build/coordinator/PROCESS-AUDIT-20261009.md:83 @worktree].
- Run the gate the change touched, chosen from the diff; an interrupted gate
  does not push [fn: build/coordinator/PROCESS-AUDIT-20261009.md:73-75 @worktree].
- A new red belongs to the batch that made it and is fixed before the next
  merge [fn: docs/proofs.md:474-476 @3bbfc4dca].
