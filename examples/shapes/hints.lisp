; examples/shapes/hints.lisp
;
; Shapes: defthm :hints with :use/:instance, :cases, :expand, :induct, and
; :in-theory (e/d ...), each after a local must-fail of the hintless
; attempt; and a subgoal hint that spells the Goal's whole theory again.
;
; Cited by ai/01-form-shapes.md, "defthm :hints".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mag (x) (if (< x 0) (- x) x))

; --- :use with :instance, and the rule it instantiates disabled in the
; same hint (an enabled rewrite rule would rewrite its own instance to T).
(defun p (x) (cons x x))
(defthm car-p (equal (car (p x)) x))
(in-theory (disable p (:type-prescription p)))

; The pitfall: the same :use with CAR-P left enabled.  Both instances
; rewrite to T and the goal is left without them (ACL2 prints a [Use]
; warning naming the rule).
(local
 (must-fail
  (thm (implies (equal (p a) (p b)) (equal a b))
       :hints (("Goal" :use ((:instance car-p (x a))
                             (:instance car-p (x b))))))))

(defthm p-injective
  (implies (equal (p a) (p b)) (equal a b))
  :hints (("Goal" :use ((:instance car-p (x a))
                        (:instance car-p (x b)))
                  :in-theory (disable car-p)))
  :rule-classes nil)

; --- :cases: split on a condition the goal does not mention.
(defthm mag-when-negative
  (implies (and (rationalp x) (< x 0)) (equal (mag x) (- x))))
(defthm mag-when-non-negative
  (implies (and (rationalp x) (<= 0 x)) (equal (mag x) x)))
(in-theory (disable mag))

(local
 (must-fail
  (thm (implies (rationalp x) (<= 0 (mag x))))))

(defthm mag-non-negative
  (implies (rationalp x) (<= 0 (mag x)))
  :hints (("Goal" :cases ((< x 0)))))

; --- :expand: open a call the rewriter declines to open.
(defun tk (n x)
  (if (zp n) nil (cons (car x) (tk (- n 1) (cdr x)))))

(local
 (must-fail
  (thm (equal (len (tk 1 x)) 1))))

(defthm len-of-tk-1
  (equal (len (tk 1 x)) 1)
  :hints (("Goal" :expand ((tk 1 x)))))

; --- :induct: name a term whose recursion is the induction to do.
(local
 (must-fail
  (thm (implies (natp n) (equal (len (tk (+ 1 n) x)) (+ 1 n))))))

(defthm len-of-tk-succ
  (implies (natp n) (equal (len (tk (+ 1 n) x)) (+ 1 n)))
  :hints (("Goal" :induct (tk n x) :expand ((tk 1 x)))))

; The better repair is the general lemma, after which no hint is needed.
(defthm len-of-tk
  (equal (len (tk n x)) (nfix n)))

; --- :in-theory (e/d ...): enable what the proof needs, disable what it
; must not open, in one expression evaluated against the current world.
(defun dbl (x) (* 2 (fix x)))
(defun half (x) (/ (fix x) 2))
(in-theory (disable dbl half))

(local
 (must-fail
  (thm (equal (half (dbl x)) (fix x)))))

(defthm half-of-dbl
  (equal (half (dbl x)) (fix x))
  :hints (("Goal" :in-theory (e/d (dbl half) (mag)))))

; --- A subgoal hint does not inherit the Goal's :in-theory: each
; :in-theory is evaluated against the world.  To keep the Goal's theory and
; add one rule at a subgoal, spell the whole e/d again.
(defthm half-of-dbl-by-cases
  (equal (half (dbl x)) (fix x))
  :hints (("Goal" :cases ((acl2-numberp x))
                  :in-theory (e/d (dbl half) (mag)))
          ("Subgoal 1" :in-theory (e/d (dbl half fix) (mag))))
  :rule-classes nil)
