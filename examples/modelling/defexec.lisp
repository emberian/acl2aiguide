; examples/modelling/defexec.lisp
;
; defexec: the guard is what makes the recursion terminate, but the
; definitional principle ignores the guard (:DOC defexec).  So the :logic
; body tests the guard and returns a default outside it, and the :exec body,
; which runs once guards are verified, omits the test.  defexec proves, in a
; local event, that the :exec body terminates whenever the guard holds.
;
; Cited by humans/03-modelling-data.md, "defexec".

(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

; The number of base-B digits of N.  FLOOR N B decreases only when B > 1,
; and B > 1 is the guard.
(defexec digit-count (n b)
  (declare (xargs :guard (and (natp n) (integerp b) (< 1 b))
                  :measure (nfix n)))
  (mbe :logic (if (and (natp n) (integerp b) (< 1 b))
                  (if (< n b) 1 (+ 1 (digit-count (floor n b) b)))
                0)
       :exec (if (< n b) 1 (+ 1 (digit-count (floor n b) b)))))

(defthm digit-count-positive
  (implies (and (natp n) (integerp b) (< 1 b))
           (< 0 (digit-count n b)))
  :rule-classes :linear)

(assert-event (equal (digit-count 255 16) 2))
(assert-event (equal (digit-count 256 16) 3))

; Outside the guard the logic answers the default, and only the logic is
; run there (guard checking off), so the default is what a proof sees.
(assert-event (with-guard-checking :none (equal (digit-count 255 1) 0)))
