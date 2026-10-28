; examples/rewriting/congruence.lisp
;
; What it shows: an equivalence relation (defequiv), a rewrite rule that holds
; only up to that equivalence, and a congruence rule (defcong) saying the
; equivalence may be used inside the first argument of CNT.  Without the
; congruence the rewriter may not use the LEQUIV rule under CNT; with it the
; goal is proved by rewriting alone (:doc equivalence, :doc congruence).
;
; Cited by humans/02-rewriting-theories-books.md, ":equivalence,
; :congruence, :refinement".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun lfix (x)
  (if (consp x) (cons (car x) (lfix (cdr x))) nil))

(defun lequiv (x y)
  (equal (lfix x) (lfix y)))

(defequiv lequiv)

(defun cnt (x)
  (if (consp x) (+ 1 (cnt (cdr x))) 0))

; A rewrite rule whose equivalence is LEQUIV, not EQUAL: it may only be used
; where LEQUIV is the equivalence to maintain.
(defthm lequiv-of-lfix
  (lequiv (lfix x) x))

(in-theory (disable lfix cnt lequiv))

(local
 (must-fail
  (thm (equal (cnt (lfix (lfix x))) (cnt x)))))

(defthm cnt-of-lfix-lemma
  (equal (cnt (lfix x)) (cnt x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable cnt lfix))))

; CNT's value is unchanged by an LEQUIV-equivalent first argument.
(defcong lequiv equal (cnt x) 1
  :hints (("Goal" :in-theory (enable lequiv)
                  :use ((:instance cnt-of-lfix-lemma (x x))
                        (:instance cnt-of-lfix-lemma (x x-equiv))))))

; Now (lfix (lfix x)) rewrites to X under CNT, twice, by LEQUIV-OF-LFIX.
(defthm cnt-of-lfix-lfix
  (equal (cnt (lfix (lfix x))) (cnt x))
  :rule-classes nil)
