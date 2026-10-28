; examples/prover/cases-hint.lisp
;
; What it shows: two conditional rewrite rules whose hypotheses split on the
; sign of X.  Nothing in the goal mentions the sign, so neither rule's
; hypothesis can be relieved and the proof fails.  A :cases hint splits the
; goal on (< x 0); each case then has the fact one rule needs.
;
; Cited by humans/01-logic-and-prover.md, "The hints: :cases".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mag (x)
  (if (< x 0) (- x) x))

(defthm mag-when-negative
  (implies (and (rationalp x) (< x 0))
           (equal (mag x) (- x))))

(defthm mag-when-not-negative
  (implies (and (rationalp x) (<= 0 x))
           (equal (mag x) x)))

(in-theory (disable mag))

(local
 (must-fail
  (thm (implies (rationalp x)
                (<= 0 (mag x))))))

; :cases ((< x 0)) produces one subgoal assuming (< x 0) and one assuming its
; negation.  The split happens at the named goal and is not inherited.
(defthm mag-non-negative
  (implies (rationalp x)
           (<= 0 (mag x)))
  :hints (("Goal" :cases ((< x 0)))))
