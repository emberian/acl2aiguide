; examples/assured/named-stop.lisp
;
; What it shows: TigerStyle's "assertions downgrade catastrophic
; correctness bugs into liveness bugs", in ACL2, against the shape fn2's
; review found most often: the absorbed refusal
; (REVIEW-SINS-20261028.md findings A1, A2: an internal call's refusal code
; bound to ?IGNORED, and the caller answering :OK).
;
; The core is one resource count and one queue count with the invariant
; FREE + QUEUED = *CAP*.  Three shapes of the same ISSUE operation:
;
;   1. ISSUE-ABSORBING: reserves a credit, enqueues, ignores the enqueue's
;      code, answers :OK.  On a state that breaks the invariant (which the
;      boundary cannot rule out if the code is wrong elsewhere) the caller
;      is told :OK, the credit is spent and nothing is queued: a leak that
;      nobody sees.  Evaluated below.
;   2. ISSUE: the internal enqueue has no refusal branch; its precondition
;      is in its guard, and ISSUE's guard (the invariant) proves it after a
;      successful reserve.  The impossible branch is deleted, not handled.
;      Proved: ISSUE preserves the invariant.
;   3. ISSUE-CHECKED: for a boundary that cannot prove the precondition
;      (an input from the host), the check stays, and its failure STOPS the
;      core with a named reason.  The first reason wins, so later fallout
;      cannot overwrite the diagnostic (fn2's CORE-STOP,
;      fn2/books/core.lisp:133-147 @127f7b877).  Proved: a stopped core
;      keeps its first reason through any later stop.
;
; Cited by assured/humans/01-rules-as-declarations.md and
; assured/ai/01-rules-as-declarations.md.

(in-package "ACL2")

(defconst *cap* 16)

; Stop reasons are named: an enum-like constant family, never a bare 3.
(defconst *stop-none* 0)
(defconst *stop-queue-full* 1)
(defconst *stop-bad-input* 2)
(defconst *stop-reason-count* 3)

(defstobj core
  (free :type (integer 0 16) :initially 16)
  (queued :type (integer 0 16) :initially 0)
  (stopped :type bit :initially 0)
  (stop-reason :type (integer 0 2) :initially 0))

(defun core-invp (core)
  (declare (xargs :stobjs core))
  (equal (+ (free core) (queued core)) *cap*))

; Boundary refusal: running out of credit is not corruption, it is a
; continuation the caller holds (fn2's :EXHAUSTED; EXECUTION-MODEL rule 3).
(defun reserve (core)
  (declare (xargs :stobjs core))
  (if (< 0 (free core))
      (let ((core (update-free (- (free core) 1) core))) (mv :ok core))
    (mv :exhausted core)))

; Shape 1's enqueue: a refusal branch that the invariant makes unreachable.
(defun enqueue-refusing (core)
  (declare (xargs :stobjs core))
  (if (< (queued core) *cap*)
      (let ((core (update-queued (+ 1 (queued core)) core))) (mv :ok core))
    (mv :full core)))

(defun issue-absorbing (core)
  (declare (xargs :stobjs core))
  (mv-let (code core) (reserve core)
    (if (not (eq code :ok))
        (mv code core)
      (mv-let (ignored core) (enqueue-refusing core)
        (declare (ignore ignored))
        (mv :ok core)))))

; A corrupt state (QUEUED already at the cap, credit still free): the
; absorbing issue answers :OK and leaks the credit.
(defun absorbing-demo ()
  (declare (xargs :guard t))
  (with-local-stobj core
    (mv-let (answer core)
      (let* ((core (update-queued 16 core))
             (core (update-free 1 core)))
        (mv-let (code core) (issue-absorbing core)
          (mv (list code (free core) (queued core)) core)))
      answer)))

(assert-event (equal (absorbing-demo) '(:ok 0 16)))

; Shape 2: the precondition is the guard; there is no :FULL branch.
(defun enqueue (core)
  (declare (xargs :stobjs core
                  :guard (< (queued core) *cap*)))
  (update-queued (+ 1 (queued core)) core))

(defun issue (core)
  (declare (xargs :stobjs core :guard (core-invp core)))
  (mv-let (code core) (reserve core)
    (if (eq code :ok)
        (let ((core (enqueue core))) (mv :ok core))
      (mv code core))))

(defthm issue-preserves-invariant
  (implies (and (corep core) (core-invp core))
           (core-invp (mv-nth 1 (issue core)))))

; Shape 3: the boundary check stays, and failure is a named stop.
(defun core-stop (reason core)
  (declare (xargs :stobjs core
                  :guard (and (natp reason) (< 0 reason)
                              (< reason *stop-reason-count*))))
  (if (= (stopped core) 1)
      core
    (let* ((core (update-stopped 1 core))
           (core (update-stop-reason reason core)))
      core)))

(defun issue-checked (n core)
  ; N is a count supplied by the host: it is validated, not trusted.
  (declare (xargs :stobjs core))
  (cond ((not (and (natp n) (<= n 1))) (let ((core (core-stop *stop-bad-input* core))) (mv :stopped core)))
        ((= n 0) (mv :ok core))
        ((not (< (queued core) *cap*))
         (let ((core (core-stop *stop-queue-full* core))) (mv :stopped core)))
        (t (mv-let (code core) (reserve core)
             (if (eq code :ok)
                 (let ((core (enqueue core))) (mv :ok core))
               (mv code core))))))

(defthm core-stop-keeps-first-reason
  (implies (equal (stopped core) 1)
           (and (equal (stopped (core-stop reason core)) 1)
                (equal (stop-reason (core-stop reason core)) (stop-reason core)))))

(defthm core-stop-records-reason
  (implies (not (equal (stopped core) 1))
           (and (equal (stopped (core-stop reason core)) 1)
                (equal (stop-reason (core-stop reason core)) reason))))

; The corrupt state from shape 1 now stops with its reason, and a second
; corruption does not overwrite it.
(defun checked-demo ()
  (declare (xargs :guard t))
  (with-local-stobj core
    (mv-let (answer core)
      (let* ((core (update-queued 16 core))
             (core (update-free 1 core)))
        (mv-let (code1 core) (issue-checked 1 core)
          (mv-let (code2 core) (issue-checked 7 core)
            (mv (list code1 code2 (stopped core) (stop-reason core) (free core))
                core))))
      answer)))

(assert-event (equal (checked-demo) (list :stopped :stopped 1 *stop-queue-full* 1)))
