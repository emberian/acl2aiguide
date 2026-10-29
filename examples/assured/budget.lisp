; examples/assured/budget.lisp
;
; What it shows: a budget as a guard and a measure, in the shape of fn2's
; DEFMACHINE budgets (fn2/books/machines.lisp:218-226 @127f7b877: each
; machine kind declares :budget (:bytes B :steps S :descriptors D), and the
; generated NAME-CHARGE refuses a preflight that exceeds a cap before any
; mutation).  TigerStyle asks that every loop and queue have a fixed upper
; bound; here the bound is (1) the measure of the run loop, so ACL2 proves
; termination from it, (2) a guard on the work step, so a verified caller
; must prove it has the budget before spending it, and (3) a theorem about
; what one run can spend.
;
;   - RUN-CHARGE: the preflight.  Answers the charge or :OVER, never a
;     partial charge.
;   - MACHINE-RUN: runs queued items while the step and byte budgets last;
;     an item that does not fit YIELDS and stays queued (no mutation for
;     it), so the next run resumes it.  The loop's measure is the remaining
;     step budget, not the queue length: a run is bounded even if the queue
;     is not.
;   - Theorems: one run spends at most the declared caps; a yielded item is
;     still at the head of the queue; the work done plus the work left is
;     the work queued (nothing lost, nothing invented).
;
; Cited by assured/humans/01-rules-as-declarations.md and
; assured/ai/01-rules-as-declarations.md.

(in-package "ACL2")

(defconst *run-bytes* 4096)
(defconst *run-steps* 32)

; Each queued item is a byte count to copy; one item costs one step.
(defun itemsp (xs)
  (declare (xargs :guard t))
  (if (atom xs) (null xs)
    (and (natp (car xs)) (itemsp (cdr xs)))))

; The preflight: either the whole charge fits under both remaining
; budgets, or nothing is charged.
(defun run-charge (bytes steps want)
  (declare (xargs :guard (and (natp bytes) (natp steps) (natp want))))
  (if (and (<= 1 steps) (<= want bytes))
      (mv t (- bytes want) (- steps 1))
    (mv nil bytes steps)))

; The work step: its guard is the budget it spends.  A caller that has not
; proved the charge fits cannot call it from verified code.
(defun copy-item (want bytes done)
  (declare (xargs :guard (and (natp want) (natp bytes) (natp done)
                              (<= want bytes))))
  (mv (- bytes want) (+ done want)))

(defun machine-run (queue bytes steps done)
  (declare (xargs :guard (and (itemsp queue) (natp bytes) (natp steps) (natp done))
                  :measure (nfix steps)))
  (if (or (atom queue) (zp steps))
      (mv :idle queue bytes steps done)
    (mv-let (okp bytes2 steps2) (run-charge bytes steps (car queue))
      (declare (ignore bytes2))
      (if (not okp)
          (mv :yield queue bytes steps done)
        (mv-let (bytes3 done3) (copy-item (car queue) bytes done)
          (machine-run (cdr queue) bytes3 steps2 done3))))))

(defun sum-items (xs)
  (declare (xargs :guard (itemsp xs)))
  (if (atom xs) 0 (+ (car xs) (sum-items (cdr xs)))))

; Spent bytes never exceed the budget the run started with.
(defthm machine-run-bytes-bounded
  (implies (and (natp bytes) (natp steps) (natp done) (itemsp queue))
           (and (natp (mv-nth 2 (machine-run queue bytes steps done)))
                (<= (mv-nth 2 (machine-run queue bytes steps done)) bytes))))

(defthm machine-run-steps-bounded
  (implies (and (natp bytes) (natp steps) (natp done) (itemsp queue))
           (<= (mv-nth 3 (machine-run queue bytes steps done)) steps)))

; Nothing lost, nothing invented: work done plus work left is constant.
(defthm machine-run-conserves-work
  (implies (and (natp bytes) (natp steps) (natp done) (itemsp queue))
           (equal (+ (mv-nth 4 (machine-run queue bytes steps done))
                     (sum-items (mv-nth 1 (machine-run queue bytes steps done))))
                  (+ done (sum-items queue)))))

; A yield leaves the item that did not fit at the head of the queue.
(defthm machine-run-yield-keeps-head
  (implies (equal (mv-nth 0 (machine-run queue bytes steps done)) :yield)
           (and (consp (mv-nth 1 (machine-run queue bytes steps done)))
                (< (mv-nth 2 (machine-run queue bytes steps done))
                   (car (mv-nth 1 (machine-run queue bytes steps done)))))))

; Every byte the run copied was charged against its byte budget.
(defthm machine-run-spends-what-it-charges
  (implies (and (natp bytes) (natp steps) (natp done) (itemsp queue))
           (equal (+ (mv-nth 4 (machine-run queue bytes steps done))
                     (mv-nth 2 (machine-run queue bytes steps done)))
                  (+ done bytes))))

; So one run from a fresh budget copies at most the declared byte cap.
(defthm one-run-within-caps
  (implies (and (itemsp queue) (natp done))
           (<= (- (mv-nth 4 (machine-run queue *run-bytes* *run-steps* done)) done)
               *run-bytes*))
  :hints (("Goal" :use ((:instance machine-run-spends-what-it-charges
                                   (bytes *run-bytes*) (steps *run-steps*))
                        (:instance machine-run-bytes-bounded
                                   (bytes *run-bytes*) (steps *run-steps*)))
                  :in-theory (disable machine-run-spends-what-it-charges
                                      machine-run-bytes-bounded))))

; Teeth.  Three items of 4000, 200 and 10 bytes: the first fits, the
; second does not fit in the 96 bytes left, so the run yields with the
; second at the head and the third untouched.
(assert-event
 (equal (mv-list 5 (machine-run '(4000 200 10) *run-bytes* *run-steps* 0))
        '(:yield (200 10) 96 31 4000)))

; The step budget bounds the run even when the queue is longer.
(assert-event
 (mv-let (status queue bytes steps done)
   (machine-run (make-list 40 :initial-element 1) *run-bytes* *run-steps* 0)
   (and (eq status :idle) (equal (len queue) 8)
        (equal bytes 4064) (equal steps 0) (equal done 32))))

; Calling the work step without the budget fact is a guard failure.
(include-book "std/testing/must-fail" :dir :system)
(must-fail
 (defun copy-without-preflight (want bytes done)
   (declare (xargs :guard (and (natp want) (natp bytes) (natp done))))
   (copy-item want bytes done)))
