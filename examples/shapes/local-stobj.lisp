; examples/shapes/local-stobj.lisp
;
; Shapes: with-local-stobj around an mv-let that binds the stobj and returns
; only the other values; a stobj argument that is a variable (bind a call
; with LET first); mv-let binding exactly the callee's values; mv-list to
; use a multiple-value call where one value is expected.  Each wrong shape is
; kept as a local must-fail of the translate error ACL2 gives it.
;
; Cited by ai/01-form-shapes.md, "with-local-stobj and mv".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defstobj scratch
  (acc :type (integer 0 *) :initially 0)
  :non-executable t)                    ; used only through with-local-stobj

(defun add-all (xs scratch)
  (declare (xargs :stobjs scratch :guard (nat-listp xs)))
  (if (endp xs)
      scratch
    (let ((scratch (update-acc (+ (car xs) (acc scratch)) scratch)))
      (add-all (cdr xs) scratch))))

; Two values out: the answer and the stobj.
(defun total-and-scratch (xs scratch)
  (declare (xargs :stobjs scratch :guard (nat-listp xs)))
  (let ((scratch (add-all xs scratch)))
    (mv (acc scratch) scratch)))

; The shape: the mv-let binds the stobj among its variables; the body
; returns the other values and does not mention the stobj.
(defun total (xs)
  (declare (xargs :guard (nat-listp xs)))
  (with-local-stobj scratch
    (mv-let (sum scratch)
      (total-and-scratch xs scratch)
      sum)))

(assert-event (equal (total '(1 2 3)) 6))

; Wrong: the body returns the local stobj.  ACL2: "Contrary to the
; declaration that it is IGNOREd, the variable SCRATCH is used in the MV-LET
; expression" (the expansion declares the stobj ignored after the mv-let).
(local
 (must-fail
  (defun total-bad-1 (xs)
    (declare (xargs :guard (nat-listp xs)))
    (with-local-stobj scratch
      (mv-let (sum scratch)
        (total-and-scratch xs scratch)
        (mv sum scratch))))))

; Wrong: a stobj argument that is a call, not a variable.  ACL2: "the
; variable SCRATCH is required, not merely a term that returns such a
; single-threaded object, so you may need to bind SCRATCH with LET".
(local
 (must-fail
  (defun total-bad-2 (xs scratch)
    (declare (xargs :stobjs scratch :guard (nat-listp xs)))
    (total-and-scratch xs (update-acc 0 scratch)))))

; Right: bind it first.
(defun total-from-zero (xs scratch)
  (declare (xargs :stobjs scratch :guard (nat-listp xs)))
  (let ((scratch (update-acc 0 scratch)))
    (total-and-scratch xs scratch)))

; Wrong: an mv-let that binds three names to a two-valued call.  ACL2:
; "The bound variable list (SUM EXTRA SCRATCH) from an MV-LET expression
; has been found not to be compatible with the ``types'' ... (NIL SCRATCH)".
(local
 (must-fail
  (defun total-bad-3 (xs scratch)
    (declare (xargs :stobjs scratch :guard (nat-listp xs)))
    (mv-let (sum extra scratch)
      (total-and-scratch xs scratch)
      (declare (ignore extra))
      (mv sum scratch)))))

; Wrong: a two-valued call in an argument position.  ACL2: "It is illegal
; to invoke PAIR-UP here because of a signature mismatch.  This function
; call returns a result of shape (MV * *) where a result of shape * is
; required."
(defun pair-up (x)
  (declare (xargs :guard t))
  (mv x (list x)))

(local
 (must-fail
  (defun first-of-pair-bad (x)
    (declare (xargs :guard t))
    (car (pair-up x)))))

; Right: mv-let, or mv-list where a single value is wanted (in a theorem or
; an assert-event, (MV-NTH 1 (PAIR-UP X)) is the logical reading).
(defun first-of-pair (x)
  (declare (xargs :guard t))
  (mv-let (a b) (pair-up x) (declare (ignore b)) a))

(assert-event (equal (mv-list 2 (pair-up 'a)) '(a (a))))

(defthm first-of-pair-is-x
  (equal (first-of-pair x) x))

(defthm second-of-pair-up
  (equal (mv-nth 1 (pair-up x)) (list x)))
