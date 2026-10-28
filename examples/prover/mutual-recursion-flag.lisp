; examples/prover/mutual-recursion-flag.lisp
;
; What it shows: ACL2 suggests no induction for functions defined by
; mutual-recursion, so a property of the clique fails with "No induction
; schemes are suggested".  make-flag (books tools/flag) defines a flag function
; that recurs as the whole clique does and a macro that proves the members'
; theorems together by its induction (:doc make-flag).
;
; Cited by humans/01-logic-and-prover.md, "Induction schemes" (tools/flag).

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "tools/flag" :dir :system)

(mutual-recursion
 (defun tcopy (x)
   (if (atom x) x (cons (car x) (lcopy (cdr x)))))
 (defun lcopy (l)
   (if (atom l) l (cons (tcopy (car l)) (lcopy (cdr l))))))

(local
 (must-fail
  (thm (equal (tcopy x) x))))

(make-flag tcopy)

; One induction on FLAG-TCOPY proves both members' theorems.  The theorems'
; variables must be the flag function's formals (here X for TCOPY, L for
; LCOPY).
(defthm-flag-tcopy
  (defthm tcopy-is-identity
    (equal (tcopy x) x)
    :flag tcopy)
  (defthm lcopy-is-identity
    (equal (lcopy l) l)
    :flag lcopy))
