; examples/rewriting/free-variables.lisp
;
; What it shows: a rewrite rule whose first hypothesis has a free variable Y.
; The rewriter binds Y by searching the context.  With :match-free :once it
; keeps the first binding it finds, which here makes the second hypothesis
; false, and the proof fails; with :match-free :all it backtracks to the other
; binding and succeeds (:doc free-variables).
;
; Cited by humans/02-rewriting-theories-books.md, "Free variables".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((rel * *) => *))
  (local (defun rel (x y) (equal x y)))
  (defthm rel-trans-once
    (implies (and (rel x y) (rel y z))
             (rel x z))
    :rule-classes ((:rewrite :match-free :once))))

; Rewriting (rel a d): X is A, Z is D, and Y is free.  The context offers
; (rel a b) before (rel a c); :once binds Y to B, and (rel b d) is not known.
(local
 (must-fail
  (thm (implies (and (rel a c) (rel a b) (rel c d))
                (rel a d)))))

(in-theory (disable rel-trans-once))

(defthm rel-trans
  (implies (and (rel x y) (rel y z))
           (rel x z))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use rel-trans-once)))

; :all tries Y = B, fails on (rel b d), backtracks to Y = C, succeeds.
(defthm rel-a-d
  (implies (and (rel a c) (rel a b) (rel c d))
           (rel a d))
  :rule-classes nil)
