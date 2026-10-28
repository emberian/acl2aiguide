; examples/prover/induct-hint.lisp
;
; What it shows: a conjecture in which no term suggests an induction (every
; recursive call has a non-variable controlling argument), so the prover gives
; up; an :induct hint supplies the induction by naming a term whose recursion
; matches.  Then the better repair: a general lemma that makes the hint
; unnecessary.
;
; Cited by humans/01-logic-and-prover.md, "The hints: :induct" and
; "Induction schemes".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun tk (n x)
  (if (zp n)
      nil
    (cons (car x) (tk (1- n) (cdr x)))))

; (tk (+ 1 n) x) has the controlling argument (+ 1 n), not a variable, so it
; suggests no induction; LEN's argument is not a variable either.
(local
 (must-fail
  (thm (implies (natp n)
                (equal (len (tk (+ 1 n) x)) (+ 1 n))))))

; :induct (tk n x) says: induct as TK recurs on N and X.  The base case then
; needs (tk 1 x) opened, which :expand supplies (see expand-hint.lisp).
(defthm len-of-tk-plus-1-by-hints
  (implies (natp n)
           (equal (len (tk (+ 1 n) x)) (+ 1 n)))
  :hints (("Goal" :induct (tk n x)
                  :expand ((tk 1 x))))
  :rule-classes nil)

; Better: the general fact, whose own induction ACL2 finds unaided.  With it
; enabled the special case needs no hints.
(defthm len-of-tk
  (equal (len (tk n x)) (nfix n)))

(defthm len-of-tk-plus-1
  (implies (natp n)
           (equal (len (tk (+ 1 n) x)) (+ 1 n)))
  :rule-classes nil)
