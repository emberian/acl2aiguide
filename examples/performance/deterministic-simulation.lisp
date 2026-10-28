; acl2aiguide example (a test book): a seeded deterministic simulation of a
; group-commit machine, with the invariant asserted after every step, a
; bounded event loop with a measure, and a mutant the run must catch.
;
; Cited by humans/05-high-performance.md, sections "Batching and group commit
; as modelled state" and "TigerStyle in ACL2" (deterministic simulation).
;
; The machine is the commit batch of fn's specs/storage.md STO-033, cut to its
; skeleton: members are prepared into the OPEN batch (bounded); a SEAL makes
; the open batch the one IN FLIGHT (one at a time); the barrier's completion
; either acknowledges every member in flight (they are then in the DURABLE
; log) or fails, which FENCES the machine and lands some prefix of the batch
; in the log without acknowledging any of it.  The invariant: every
; acknowledged member is in the log, in order (ACKED is a prefix of DURABLE),
; and while not fenced nothing in the log is unacknowledged.
;
; What it shows:
;   - the step function is total over any event, and refuses by name;
;   - the event list comes from a seeded linear congruential generator, so a
;     failing run is replayed exactly from its seed (TigerBeetle's VOPR
;     discipline, paper tigerbeetle2026-internals-vopr.md);
;   - the checking loop is bounded by its event list (measure: len) and the
;     list by *max-events*; it answers :ok or the first violating step;
;   - a MUTANT step that acknowledges at the seal, before the barrier, is
;     caught by the same run: a checker that cannot fail is not a checker;
;   - the invariant is also PROVED for the real step, which is what the
;     simulation cannot do; the simulation is for what the proof does not
;     cover (here, nothing; in a node, the host).

(in-package "ACL2")

(include-book "std/lists/prefixp" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/append" :dir :system)

(defconst *batch-max* 8)
(defconst *max-events* 4096)

; State: (OPEN INFLIGHT DURABLE ACKED FENCED).
(defun gc-open (s) (declare (xargs :guard (true-listp s))) (nth 0 s))
(defun gc-inflight (s) (declare (xargs :guard (true-listp s))) (nth 1 s))
(defun gc-durable (s) (declare (xargs :guard (true-listp s))) (nth 2 s))
(defun gc-acked (s) (declare (xargs :guard (true-listp s))) (nth 3 s))
(defun gc-fenced (s) (declare (xargs :guard (true-listp s))) (nth 4 s))

(defun gc-make (open inflight durable acked fenced)
  (declare (xargs :guard t))
  (list open inflight durable acked fenced))

(defconst *gc-init* (gc-make nil nil nil nil nil))

(defun gc-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s)
       (equal (len s) 5)
       (true-listp (gc-open s))
       (true-listp (gc-inflight s))
       (true-listp (gc-durable s))
       (true-listp (gc-acked s))
       (booleanp (gc-fenced s))
       (<= (len (gc-open s)) *batch-max*)
       (<= (len (gc-inflight s)) *batch-max*)))

; The step.  Events: (:prepare K) (:seal) (:sync-ok) (:sync-fail J).  Any
; other value, and any event the state does not admit, leaves the state as
; it was; the answer word says which.
(defun gc-step (ev s)
  (declare (xargs :guard (gc-statep s)))
  (let ((open (gc-open s)) (inflight (gc-inflight s))
        (durable (gc-durable s)) (acked (gc-acked s)) (fenced (gc-fenced s))
        (kind (and (consp ev) (car ev))))
    (cond (fenced (mv :fenced s))
          ((eq kind :prepare)
           (if (>= (len open) *batch-max*)
               (mv :batch-full s)
             (mv :ok (gc-make (append open (list (and (consp (cdr ev)) (cadr ev))))
                              inflight durable acked fenced))))
          ((eq kind :seal)
           (if (or (consp inflight) (atom open))
               (mv :nothing-to-seal s)
             (mv :ok (gc-make nil open durable acked fenced))))
          ((eq kind :sync-ok)
           (if (atom inflight)
               (mv :nothing-in-flight s)
             (mv :ok (gc-make open nil (append durable inflight)
                              (append acked inflight) fenced))))
          ((eq kind :sync-fail)
           (if (atom inflight)
               (mv :nothing-in-flight s)
             (let ((j (if (and (consp (cdr ev)) (natp (cadr ev)))
                          (min (cadr ev) (len inflight))
                        0)))
               (mv :uncertain (gc-make open nil (append durable (take j inflight))
                                       acked t)))))
          (t (mv :unknown-event s)))))

; The MUTANT: acknowledges at the seal, before any barrier.
(defun gc-step-mutant (ev s)
  (declare (xargs :guard (gc-statep s)))
  (if (and (consp ev) (eq (car ev) :seal)
           (not (gc-fenced s)) (atom (gc-inflight s)) (consp (gc-open s)))
      (mv :ok (gc-make nil (gc-open s) (gc-durable s)
                       (append (gc-acked s) (gc-open s)) nil))
    (gc-step ev s)))

(defun gc-invp (s)
  (declare (xargs :guard (gc-statep s)))
  (and (prefixp (gc-acked s) (gc-durable s))
       (or (gc-fenced s) (equal (gc-acked s) (gc-durable s)))))

; ---------------------------------------------------------------------------
; The proof the simulation complements.

(defthm gc-statep-of-gc-step
  (implies (gc-statep s)
           (gc-statep (mv-nth 1 (gc-step ev s)))))

(local (defthm nthcdr-of-len-and-append
         (equal (nthcdr (len x) (append x y)) y)))

(defthm gc-step-preserves-invariant
  (implies (and (gc-statep s) (gc-invp s))
           (gc-invp (mv-nth 1 (gc-step ev s))))
  :hints (("Goal" :in-theory (disable prefixp-when-equal-lengths))))

(verify-guards gc-step-mutant)

; ---------------------------------------------------------------------------
; The generator: a seeded LCG over 2^31, one event per draw.

(local (include-book "arithmetic-5/top" :dir :system))

(defun lcg-next (seed)
  (declare (xargs :guard (natp seed)))
  (mod (+ (* 1103515245 seed) 12345) 2147483648))

(defthm natp-of-lcg-next
  (implies (natp seed) (natp (lcg-next seed)))
  :rule-classes :type-prescription)

(in-theory (disable lcg-next))

(defun lcg-event (seed)
  (declare (xargs :guard (natp seed)))
  (let ((r (mod (floor seed 65536) 1000)))
    (cond ((< r 700) (list :prepare (mod seed 1000)))
          ((< r 850) (list :seal))
          ((< r 999) (list :sync-ok))
          (t (list :sync-fail (mod seed 9))))))

; N events from SEED, N bounded by *max-events*.
(defun gen-events (seed n)
  (declare (xargs :guard (and (natp seed) (natp n) (<= n *max-events*))))
  (if (zp n)
      nil
    (let ((next (lcg-next seed)))
      (cons (lcg-event next) (gen-events next (- n 1))))))

; ---------------------------------------------------------------------------
; The checking run: the invariant after every step; the first violation
; answers its step number and event.  MUTANTP selects the mutant step.

(defun run-check (events s i mutantp)
  (declare (xargs :guard (and (gc-statep s) (natp i))
                  :measure (len events)))
  (cond ((atom events) :ok)
        (t (mv-let (word s2)
             (if mutantp (gc-step-mutant (car events) s) (gc-step (car events) s))
             (declare (ignore word))
             (if (and (gc-statep s2) (gc-invp s2))
                 (run-check (cdr events) s2 (+ 1 i) mutantp)
               (list :violated-at i (car events)))))))

; Every seed from 1 to K, each run of N events.
(defun all-seeds-ok (k n mutantp)
  (declare (xargs :guard (and (natp k) (natp n) (<= n *max-events*))))
  (if (zp k)
      :ok
    (let ((r (run-check (gen-events k n) *gc-init* 0 mutantp)))
      (if (eq r :ok)
          (all-seeds-ok (- k 1) n mutantp)
        (list :seed k r)))))

; The real step holds its invariant over 50 seeds of 2,000 events each.
(assert-event (eq (all-seeds-ok 50 2000 nil) :ok))

; The mutant is caught, at a seed and step the run names.  The run is
; deterministic, so the report is a constant: seed 50, step 28, a seal.
(assert-event (equal (all-seeds-ok 50 2000 t)
                     '(:seed 50 (:violated-at 28 (:seal)))))

; The run exercises every answer: the generator is not stuck in one corner.
(defun answers (events s acc)
  (declare (xargs :guard (and (gc-statep s) (true-listp acc))
                  :measure (len events)))
  (if (atom events)
      acc
    (mv-let (word s2) (gc-step (car events) s)
      (answers (cdr events)
               (if (gc-statep s2) s2 s)
               (if (member-eq word acc) acc (cons word acc))))))

(assert-event (subsetp-eq '(:ok :batch-full :nothing-to-seal :nothing-in-flight
                            :uncertain :fenced)
                          (answers (gen-events 7 2000) *gc-init* nil)))
