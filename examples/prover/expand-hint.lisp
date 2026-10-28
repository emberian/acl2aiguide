; examples/prover/expand-hint.lisp
;
; What it shows: a call of a recursive function on a constant argument that
; the rewriter declines to open, so the proof fails with "No induction schemes
; are suggested"; an :expand hint opens exactly that call.
;
; Cited by humans/01-logic-and-prover.md, "The hints: :expand".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun tk (n x)
  (if (zp n)
      nil
    (cons (car x) (tk (1- n) (cdr x)))))

; (tk 1 x) would open to (cons (car x) (tk 0 (cdr x))), but the opened body
; introduces the new argument (cdr x), and the definition heuristics refuse.
; Nothing in the goal suggests an induction either.
(local
 (must-fail
  (thm (equal (len (tk 1 x)) 1))))

; Name the term to open.  The hint applies to this goal and its descendants.
(defthm len-of-tk-1
  (equal (len (tk 1 x)) 1)
  :hints (("Goal" :expand ((tk 1 x)))))
