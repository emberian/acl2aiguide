; examples/shapes/stobj-let.lisp
;
; Shapes: a parent stobj with a child-stobj field; stobj-let to write the
; child and update the parent in one form, and to read a child field into an
; ordinary value; the direct call of the child accessor that ACL2 refuses.
;
; Cited by ai/01-form-shapes.md, "stobj-let".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defstobj kid (n :type (integer 0 *) :initially 0))

(defstobj par
  (k :type kid)                                   ; a child stobj
  (ops :type (integer 0 *) :initially 0))

; Write: bindings, producer variables, producer, consumer.  The producer
; may not mention PAR; the consumer may not mention KID.
(defun par-bump (par)
  (declare (xargs :stobjs par))
  (stobj-let
   ((kid (k par)))                        ; bind KID to the child of PAR
   (kid)                                  ; the producer returns KID
   (update-n (+ 1 (n kid)) kid)           ; producer
   (update-ops (+ 1 (ops par)) par)))     ; consumer, after PAR gets KID back

; Read: the producer variable is an ordinary value, so PAR is not updated.
(defun par-n (par)
  (declare (xargs :stobjs par))
  (stobj-let
   ((kid (k par)))
   (v)
   (n kid)
   v))

; Wrong: a direct call of the accessor of a stobj-typed field.  ACL2 says
; "The form (K PAR) is being used, as an argument to a call of N, where the
; single-threaded object KID is required ... you may need to bind KID with
; LET"; for a child stobj the binding form is stobj-let, as above.
(local
 (must-fail
  (defun par-n-bad (par)
    (declare (xargs :stobjs par))
    (n (k par)))))

(assert-event (and (eq (symbol-class 'par-bump (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'par-n (w state)) :common-lisp-compliant)))

(defthm par-n-of-par-bump
  (implies (parp par)
           (equal (par-n (par-bump par)) (+ 1 (par-n par)))))

(defun demo-par ()
  (declare (xargs :guard t))
  (with-local-stobj par
    (mv-let (r par)
      (let* ((par (par-bump par))
             (par (par-bump par)))
        (mv (list (par-n par) (ops par)) par))
      r)))

(assert-event (equal (demo-par) '(2 2)))
