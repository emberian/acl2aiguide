; examples/shapes/defun-guards.lisp
;
; Shapes: defun with :guard and :measure; :verify-guards nil and a later
; verify-guards with :guard-hints; a guard lemma stated :rule-classes nil and
; supplied by :use (never a rewrite rule).
;
; Cited by ai/01-form-shapes.md, "defun".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; :guard and :measure.  The guard is a term over the formals; the measure must
; be an o-p that decreases on every recursive call under the rulers.
(defun count-down (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (count-down (- n 1) (cons n acc))))

(assert-event (equal (count-down 3 nil) '(1 2 3)))

; The guard of a caller must imply the guard of every callee.  Here the
; guard is too weak, and guard verification fails at admission.
(local
 (must-fail
  (defun sum-all (x)
    (declare (xargs :guard (true-listp x)))
    (if (endp x) 0 (+ (car x) (sum-all (cdr x)))))))

; A callee whose guard asks more than type reasoning knows about a sum.
(defun nat-add (a b)
  (declare (xargs :guard (and (natp a) (natp b))))
  (+ a b))

; :verify-guards nil admits the logic now and defers the guard proof.
(defun sum-nats (x)
  (declare (xargs :guard (nat-listp x) :verify-guards nil))
  (if (endp x) 0 (nat-add (car x) (sum-nats (cdr x)))))

(assert-event (eq (symbol-class 'sum-nats (w state)) :ideal))

; The fact the guard proof needs, stated once, :rule-classes nil, and used
; by :use in the one verify-guards that needs it.
(defthm natp-of-sum-nats
  (implies (nat-listp x) (natp (sum-nats x)))
  :rule-classes nil)

; Without the fact, the guard conjecture needs (NATP (SUM-NATS (CDR X))),
; which only an induction proves; with induction turned off it is refused.
(local
 (must-fail
  (verify-guards sum-nats :hints (("Goal" :do-not-induct t)))))

(verify-guards sum-nats
  :hints (("Goal" :use ((:instance natp-of-sum-nats (x (cdr x)))))))

(assert-event (eq (symbol-class 'sum-nats (w state)) :common-lisp-compliant))

; Guard hints on the defun itself go in :guard-hints, not :hints (which are for
; the termination proof).  This guard proves without the hint; the keyword is
; the place to put one.
(defun sum-nats-acc (x acc)
  (declare (xargs :guard (and (nat-listp x) (natp acc))
                  :guard-hints (("Goal" :in-theory (enable nat-listp)))))
  (if (endp x) acc (sum-nats-acc (cdr x) (+ (car x) acc))))

(assert-event (equal (sum-nats-acc '(1 2 3) 0) 6))
