; examples/rewriting/linear.lisp
;
; What it shows: a bound that linear arithmetic cannot use when it is not a
; :linear rule, and the same bound stored as a :linear rule, which the linear
; arithmetic procedure adds when it considers the term (cnt (firsts x)).
;
; Cited by humans/02-rewriting-theories-books.md, ":linear".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun cnt (x)
  (if (consp x) (+ 1 (cnt (cdr x))) 0))

(defun firsts (x)
  (if (and (consp x) (consp (cdr x)))
      (cons (car x) (firsts (cddr x)))
    nil))

; FIRSTS recurs by CDDR; induct the way it recurs.
(defthm cnt-firsts-bound
  (<= (cnt (firsts x)) (cnt x))
  :rule-classes nil
  :hints (("Goal" :induct (firsts x))))

; With CNT and FIRSTS closed and no :linear fact, the inequality is unknown.
(local
 (must-fail
  (thm (implies (< (cnt x) 10)
                (< (cnt (firsts x)) 11))
       :hints (("Goal" :in-theory (disable cnt firsts))))))

(defthm cnt-firsts-linear
  (<= (cnt (firsts x)) (cnt x))
  :rule-classes :linear
  :hints (("Goal" :use cnt-firsts-bound)))

(defthm cnt-firsts-under-11
  (implies (< (cnt x) 10)
           (< (cnt (firsts x)) 11))
  :hints (("Goal" :in-theory (disable cnt firsts)))
  :rule-classes nil)
