; examples/fn-lessons/local-stobj-shape.lisp
;
; What it shows: the two stobj shapes an fn lane paid an attempt each to
; learn.  (1) with-local-stobj's body is an mv-let that binds the stobj and
; returns the OTHER values, never the stobj.  (2) a stobj formal takes only
; the stobj variable itself as its actual argument, so an updated stobj is
; bound with let first (:doc with-local-stobj, :doc stobj).
;
; Cited by fn-lessons/16-local-stobjs-and-the-repl.md, "The shape to copy".

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defstobj tally (tally-n :type (integer 0 *) :initially 0))

(defun tally-add-all (xs tally)
  (declare (xargs :stobjs tally :guard (nat-listp xs)))
  (if (consp xs)
      (let ((tally (update-tally-n (+ (car xs) (tally-n tally)) tally)))
        (tally-add-all (cdr xs) tally))
    tally))

; Right: the mv-let binds TALLY and returns only TOTAL.
(defun sum-with-local-tally (xs)
  (declare (xargs :guard (nat-listp xs)))
  (with-local-stobj
   tally
   (mv-let (total tally)
     (let ((tally (tally-add-all xs tally)))
       (mv (tally-n tally) tally))
     total)))

(assert-event (equal (sum-with-local-tally '(1 2 3)) 6))

; Wrong: returning the local stobj from the body.
(local
 (must-fail
  (defun returns-local-tally (xs)
    (declare (xargs :guard (nat-listp xs)))
    (with-local-stobj
     tally
     (mv-let (total tally)
       (let ((tally (tally-add-all xs tally)))
         (mv (tally-n tally) tally))
       (mv total tally))))))

; Wrong: a call in a stobj argument position.
(local
 (must-fail
  (defun restart-and-add (xs tally)
    (declare (xargs :stobjs tally :guard (nat-listp xs)))
    (tally-add-all xs (update-tally-n 0 tally)))))

; Right: bind the updated stobj first.
(defun restart-and-add (xs tally)
  (declare (xargs :stobjs tally :guard (nat-listp xs)))
  (let ((tally (update-tally-n 0 tally)))
    (tally-add-all xs tally)))
