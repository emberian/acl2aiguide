; examples/systems/generic-fold.lisp
;
; A generic layer by encapsulate and functional instantiation.  A monoid is
; constrained (an operation, its identity, associativity, identity laws);
; a fold over it is defined; a theorem is proved about the fold from the
; constraints alone; and two instances (natural addition, list append)
; obtain it by :functional-instance, discharging only the constraints.
; tools/def-functional-instance writes the second instance's event.
;
; Cited by humans/04-modelling-systems.md, "Functional instantiation and
; generic layers".

(in-package "ACL2")
(include-book "tools/def-functional-instance" :dir :system)

(encapsulate
  (((mop * *) => *)
   ((mid) => *))
  ; The witness proves the constraints consistent; it is local, so nothing
  ; outside knows MOP is addition.
  (local (defun mop (x y) (+ (fix x) (fix y))))
  (local (defun mid () 0))
  ; The constraints are what every instance must prove, so they are stated
  ; as weakly as the generic theorem allows: the identity is only required
  ; to be neutral on RESULTS of MOP (plus-fix and app below fix their
  ; arguments, so (MOP (MID) X) is not X for every X).
  (defthm mop-assoc
    (equal (mop (mop x y) z) (mop x (mop y z))))
  (defthm mop-left-id
    (equal (mop (mid) x) (mop x (mid))))
  (defthm mop-right-id-on-results
    (equal (mop (mop x y) (mid)) (mop x y)))
  (defthm mop-id-idem
    (equal (mop (mid) (mid)) (mid))))

; The fold is an ordinary definition over the constrained functions.
(defun mfold (xs)
  (if (atom xs) (mid) (mop (car xs) (mfold (cdr xs)))))

; Folding a constant: disable its executable counterpart, since it calls
; constrained functions that cannot be evaluated (:DOC
; functional-instantiation-example gives the same advice).
(in-theory (disable (:executable-counterpart mfold)))

; The identity is neutral on every fold result: a fold result is (MID) or a
; MOP result.
(defthm mop-mfold-mid
  (equal (mop (mfold ys) (mid)) (mfold ys))
  :hints (("Goal" :expand ((mfold ys)))))

; The generic theorem, from the constraints only.
(defthm mfold-of-append
  (equal (mfold (append xs ys))
         (mop (mfold xs) (mfold ys)))
  :hints (("Goal" :induct (mfold xs))))

; ---------------------------------------------------------------------------
; Instance 1: sum of a list, by :functional-instance in a :use hint.  The
; obligations are the constraints with MOP := plus-fix, MID := 0 and the
; definition of MFOLD with MFOLD := sum-list.

(defun plus-fix (x y) (+ (fix x) (fix y)))

(defun sum-list (xs)
  (if (atom xs) 0 (plus-fix (car xs) (sum-list (cdr xs)))))

(defthm sum-list-of-append
  (equal (sum-list (append xs ys))
         (plus-fix (sum-list xs) (sum-list ys)))
  :hints (("Goal" :use ((:functional-instance mfold-of-append
                                              (mop plus-fix)
                                              (mid (lambda () 0))
                                              (mfold sum-list))))))

; ---------------------------------------------------------------------------
; Instance 2: concatenation of a list of lists, by def-functional-instance,
; which reads MFOLD-OF-APPEND from the world and writes the instance.

(defun app (x y) (append (true-list-fix x) (true-list-fix y)))

(defun concat-all (xss)
  (if (atom xss) nil (app (car xss) (concat-all (cdr xss)))))

(def-functional-instance concat-all-of-append
  mfold-of-append
  ((mop app) (mid (lambda () nil)) (mfold concat-all)))

; The instance is a theorem about the concrete functions, with no
; constrained function left in it.
(assert-event
 (equal (getpropc 'concat-all-of-append 'untranslated-theorem nil (w state))
        '(equal (concat-all (append xs ys))
                (app (concat-all xs) (concat-all ys)))))

(assert-event (equal (concat-all '((1 2) (3) nil (4))) '(1 2 3 4)))

; A substitution that does NOT meet the constraints is refused.  With MOP
; := subtraction the instance owes the constraints under the substitution,
; and the identity constraint MOP-LEFT-ID becomes (- 0 X) = (- X 0), which
; ACL2 reduces to (IMPLIES (ACL2-NUMBERP X) (EQUAL (- X) X)) and cannot
; prove: the hint fails, so the theorem does.
(include-book "std/testing/must-fail" :dir :system)
(defun minus-list (xs)
  (if (atom xs) 0 (- (fix (car xs)) (minus-list (cdr xs)))))
(must-fail
 (defthm minus-list-of-append
   (equal (minus-list (append xs ys))
          (- (minus-list xs) (minus-list ys)))
   :hints (("Goal" :use ((:functional-instance mfold-of-append
                                               (mop (lambda (x y) (- (fix x) (fix y))))
                                               (mid (lambda () 0))
                                               (mfold minus-list)))))))
