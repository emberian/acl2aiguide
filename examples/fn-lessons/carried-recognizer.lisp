; examples/fn-lessons/carried-recognizer.lisp
;
; What it shows: fn's rule that a whole-state recognizer guards the
; executable path and is never recomputed per operation.  The recognizer
; IDS-OKP is quadratic (a member test per element).  ADD-ID keeps the total
; logical definition (a non-state is returned unchanged in the logic) and
; its :exec path skips the test, relying on the guard; a preservation
; theorem is the guard proof of every caller, so a loop carries the
; invariant instead of rechecking it (:doc mbe, :doc guard,
; :doc verify-guards).  Note that a top-level call of a guard-verified
; function still evaluates its guard once (:doc guard-evaluation-table,
; c1): the entry the host calls is where the cost of the guard is paid.
;
; Cited by fn-lessons/08-whole-state-recognizers.md, "The shape to copy".

(in-package "ACL2")

; Its guard is T: the :logic half of ADD-ID's mbe calls it on any value.
(defun ids-okp (s)
  (declare (xargs :guard t))
  (if (consp s)
      (and (natp (car s))
           (true-listp (cdr s))
           (not (member-equal (car s) (cdr s)))
           (ids-okp (cdr s)))
    (null s)))

(defthm ids-okp-forward-true-listp
  (implies (ids-okp s) (true-listp s))
  :rule-classes :forward-chaining)

(defun add-id (id s)
  (declare (xargs :guard (ids-okp s) :verify-guards nil))
  (if (mbe :logic (not (ids-okp s)) :exec nil)
      s
    (if (and (natp id) (not (member-equal id s)))
        (cons id s)
      s)))

(defthm ids-okp-of-add-id
  (implies (ids-okp s)
           (ids-okp (add-id id s))))

(verify-guards add-id)

; The loop's guard proof is the preservation theorem: IDS-OKP is checked by
; the caller of ADD-IDS once, and never inside the loop.
(defun add-ids (ids s)
  (declare (xargs :guard (and (true-listp ids) (ids-okp s))))
  (if (consp ids)
      (add-ids (cdr ids) (add-id (car ids) s))
    s))

(assert-event (equal (add-ids '(1 2 1 3) nil) '(3 2 1)))
