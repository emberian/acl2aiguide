; examples/assured/nth-cost.lisp
;
; What it shows: the rule family that cost fn2 most of its certification
; time, reproduced at a size that certifies in about a second, and the fix
; (fn2 commit 1fa1fe24b, "fn2 W1: every book in the layer-A closure
; certifies under one minute": the generic numeric-array NTH type/linear
; rules, one per array column, "match every (nth i xs)"; sum of book times
; 1,876 s before, 284 s after).
;
; A generator that emits, per array column K,
;   GENERIC:  (implies (and (arr-pK xs) (natp i) (< i (len xs)))
;                      (< (nth i xs) 2^limK))                 ; any xs
;   SPECIFIC: (implies (and (arr-pK (nth K r)) (natp i) (< i (len (nth K r))))
;                      (< (nth i (nth K r)) 2^limK))          ; field K only
; gives the linear-arithmetic procedure, for every NTH term of every goal,
; one candidate per column from the generic family.  The specific family
; offers each term exactly one candidate.  The theorem FIELD-SUM-BOUND,
; over all N fields of a record, is proved twice below: once with only the
; specific rules (FIELD-SUM-BOUND-SPECIFIC) and once with both families
; enabled (FIELD-SUM-BOUND-BOTH).
;
; Measured on the laptop (ACL2 8.7, SBCL 2.6.8, 2026-10-29), the prover's
; Time and step count for the two proofs at N fields:
;
;     N    specific only            both families
;     12   0.00 s,  1,164 steps     0.04 s, 1,659 steps
;     24   0.01 s,  2,292 steps     0.50 s, 3,879 steps
;     36   0.02 s,  3,420 steps     2.07 s, 6,675 steps
;
; Two lessons.  The specific family grows linearly in N and the generic one
; about fiftyfold from N = 12 to N = 36.  And the step count does not track
; the time: at N = 36 the generic proof takes a hundred times as long as
; the specific one for about twice the steps, so a prover-step budget set
; from the specific proof would not have caught this family.  This book
; uses N = 24.
;
; Cited by assured/humans/04-certify-cost.md and assured/ai/04-certify-cost.md.

(in-package "ACL2")

(defun nc-sym2 (s n)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol
   (coerce (append (coerce s 'list) (explode-atom n 10)) 'string) 'acl2))

(defun nc-column-events (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (let ((p (nc-sym2 "ARR-P" n)) (lim (+ 8 n)))
      (append
       (nc-column-events (- n 1))
       `((defun ,p (xs)
           (if (atom xs) (null xs)
             (and (natp (car xs)) (< (car xs) (expt 2 ,lim)) (,p (cdr xs)))))
         (defthm ,(nc-sym2 "GENERIC-NTH-NATP" n)
           (implies (and (,p xs) (natp i) (< i (len xs))) (natp (nth i xs)))
           :rule-classes :type-prescription)
         (defthm ,(nc-sym2 "GENERIC-NTH-BOUND" n)
           (implies (and (,p xs) (natp i) (< i (len xs))) (< (nth i xs) (expt 2 ,lim)))
           :rule-classes :linear)
         (defthm ,(nc-sym2 "FIELD-NTH-NATP" n)
           (implies (and (,p (nth ,n r)) (natp i) (< i (len (nth ,n r))))
                    (natp (nth i (nth ,n r))))
           :rule-classes :type-prescription)
         (defthm ,(nc-sym2 "FIELD-NTH-BOUND" n)
           (implies (and (,p (nth ,n r)) (natp i) (< i (len (nth ,n r))))
                    (< (nth i (nth ,n r)) (expt 2 ,lim)))
           :rule-classes :linear)
         (in-theory (disable ,p)))))))

(defun nc-generic-runes (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (list* `(:type-prescription ,(nc-sym2 "GENERIC-NTH-NATP" n))
           `(:linear ,(nc-sym2 "GENERIC-NTH-BOUND" n))
           (nc-generic-runes (- n 1)))))

(defun nc-terms (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons `(nth i (nth ,n r)) (nc-terms (- n 1)))))

(defun nc-hyps (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (list* `(,(nc-sym2 "ARR-P" n) (nth ,n r)) `(< i (len (nth ,n r)))
           (nc-hyps (- n 1)))))

(defmacro nc-columns (n) (cons 'progn (nc-column-events n)))
(defmacro nc-field-sum-bound (n)
  `(implies (and (natp i) ,@(nc-hyps n))
            (< (+ ,@(nc-terms n)) (expt 2 60))))
(defmacro nc-generic (enable-p n)
  `(in-theory (,(if enable-p 'enable 'disable) ,@(nc-generic-runes n))))

(nc-columns 24)

; The fix: the generic family is disabled after the generator used it;
; the field-specific family stays enabled.
(nc-generic nil 24)

(defthm field-sum-bound-specific
  (nc-field-sum-bound 24)
  :rule-classes nil)

; The same theorem with the generic family enabled again: it still proves,
; about fifty times slower at this size (see the table above).
(nc-generic t 24)

(defthm field-sum-bound-both
  (nc-field-sum-bound 24)
  :rule-classes nil)
