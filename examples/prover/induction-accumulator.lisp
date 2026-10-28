; examples/prover/induction-accumulator.lisp
;
; What it shows: an induction proof whose first attempt fails because the
; conjecture is too specific (the accumulator is the constant NIL), and the
; fix: prove the generalization, from which the specific theorem follows by
; rewriting with no induction at all.
;
; Cited by humans/01-logic-and-prover.md, "Why proofs fail: the induction was
; right but the statement was too weak".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun rv (x)
  (if (consp x)
      (append (rv (cdr x)) (list (car x)))
    nil))

(defun rva (x acc)
  (if (consp x)
      (rva (cdr x) (cons (car x) acc))
    acc))

; First attempt: the induction hypothesis is about (rva (cdr x) nil), but the
; induction step needs a fact about (rva (cdr x) (list (car x))).  The prover
; pushes sub-inductions and fails.  The step limit keeps the failure cheap.
(local
 (must-fail
  (with-prover-step-limit 200000
    (thm (equal (rva x nil) (rv x))))))

; The fix: state the theorem for every accumulator.  Now the induction
; hypothesis is about (rva (cdr x) (cons (car x) acc)) for the new ACC, which is
; exactly what the step needs.
(defthm rva-is-rv-append
  (equal (rva x acc)
         (append (rv x) acc)))

; The specific theorem is now a rewrite away.
(defthm rva-nil-is-rv
  (equal (rva x nil) (rv x)))
