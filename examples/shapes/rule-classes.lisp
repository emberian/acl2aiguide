; examples/shapes/rule-classes.lisp
;
; Shapes: defthm with each everyday rule class -- :rewrite (the default, and
; with :corollary), :type-prescription, :forward-chaining with
; :trigger-terms, :linear, :definition, :induction, :compound-recognizer,
; :equivalence and :congruence (via defequiv/defcong), and :rule-classes nil.
; Each rule is followed by a theorem that needs it, proved with the rule and
; refused (local must-fail) where the rule is disabled.
;
; Cited by ai/01-form-shapes.md, "defthm and its rule classes".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun rv (x)
  (if (consp x) (append (rv (cdr x)) (list (car x))) nil))

(defun cnt (x)
  (if (consp x) (+ 1 (cnt (cdr x))) 0))

; :rewrite, the default class: rewrite the left side to the right side.
(defthm cnt-of-append
  (equal (cnt (append x y)) (+ (cnt x) (cnt y))))

; :rewrite with :corollary: state it for the reader, store it for the prover.
(defthm cnt-of-rv
  (equal (cnt (rv x)) (cnt x))
  :rule-classes ((:rewrite :corollary (equal (cnt (rv x)) (cnt x)))))

; :type-prescription: a type fact, used by type reasoning (no rewriting of
; its hypotheses).
(defun firsts (x)
  (if (consp x) (cons (car x) (firsts (cddr x))) nil))

(defthm true-listp-of-firsts
  (true-listp (firsts x))
  :rule-classes :type-prescription)

; :forward-chaining: when the trigger term appears, add the conclusion to
; the context (hypotheses relieved by type reasoning, not rewriting).
(defun okp (x) (and (consp x) (integerp (car x))))
(in-theory (disable okp))

(defthm okp-forward
  (implies (okp x) (and (consp x) (integerp (car x))))
  :rule-classes ((:forward-chaining :trigger-terms ((okp x))))
  :hints (("Goal" :in-theory (enable okp))))

; With the forward-chaining rule off (and the tau system, which proved the
; goal without the rule), the same goal is refused.
(local
 (must-fail
  (thm (implies (okp x) (acl2-numberp (car x)))
       :hints (("Goal" :in-theory (disable okp-forward (tau-system)))))))

(defthm okp-car-is-a-number
  (implies (okp x) (acl2-numberp (car x))))

; :linear: an inequality for linear arithmetic, stored under its maximal
; terms.
(defthm cnt-firsts-bound
  (<= (cnt (firsts x)) (cnt x))
  :rule-classes :linear)

(local
 (must-fail
  (thm (< (cnt (firsts x)) (+ 1 (cnt x)))
       :hints (("Goal" :do-not-induct t
                       :in-theory (disable cnt-firsts-bound cnt firsts))))))

(defthm cnt-firsts-below-plus-one
  (< (cnt (firsts x)) (+ 1 (cnt x)))
  :hints (("Goal" :do-not-induct t :in-theory (disable cnt firsts))))

; :definition: an alternative definition, used in place of the original
; once the original is disabled.
(defthm cnt-two-at-a-time
  (equal (cnt x)
         (if (consp x)
             (if (consp (cdr x)) (+ 2 (cnt (cddr x))) 1)
           0))
  :rule-classes ((:definition :controller-alist ((cnt t)))))

; :induction: link a pattern to an induction scheme (no proof obligation).
(defun drop (n x)
  (if (zp n) x (drop (- n 1) (cdr x))))

(defun tk (n x)
  (if (zp n) nil (cons (car x) (tk (- n 1) (cdr x)))))

(defthm drop-suggests-tk-induction
  t
  :rule-classes ((:induction :pattern (drop n x) :scheme (tk n x))))

; :compound-recognizer: tell type reasoning what a recognizer implies.
(defun smallp (x) (and (integerp x) (<= 0 x) (< x 256)))

(defthm smallp-compound-recognizer
  (implies (smallp x) (and (integerp x) (<= 0 x)))
  :rule-classes :compound-recognizer)

; :equivalence and :congruence, written by defequiv and defcong.
(defun lfix (x) (if (consp x) (cons (car x) (lfix (cdr x))) nil))
(defun lequiv (x y) (equal (lfix x) (lfix y)))
(defequiv lequiv)

; A rewrite rule whose equivalence is LEQUIV: usable only where LEQUIV is
; the equivalence being maintained.
(defthm lfix-under-lequiv (lequiv (lfix x) x))

(in-theory (disable lfix lequiv))

(defthm cnt-of-lfix-direct
  (equal (cnt (lfix x)) (cnt x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable lfix))))

; The congruence: CNT's value is unchanged by an LEQUIV-equal argument.
(defcong lequiv equal (cnt x) 1
  :hints (("Goal" :in-theory (enable lequiv)
                  :use ((:instance cnt-of-lfix-direct (x x))
                        (:instance cnt-of-lfix-direct (x x-equiv))))))

; Now LFIX-UNDER-LEQUIV rewrites inside CNT: no induction, no hint.
(defthm cnt-of-lfix-lfix
  (equal (cnt (lfix (lfix x))) (cnt x))
  :hints (("Goal" :do-not-induct t)))

; :rule-classes nil: a theorem and no rule; cited by :use or :by only.
(defthm cnt-of-rv-rv-fact
  (equal (cnt (rv (rv x))) (cnt x))
  :rule-classes nil)

(assert-event (equal (cnt (rv '(a b c))) 3))
