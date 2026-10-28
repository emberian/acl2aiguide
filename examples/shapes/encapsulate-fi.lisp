; examples/shapes/encapsulate-fi.lisp
;
; Shapes: encapsulate with a signature, a LOCAL witness definition and a
; local lemma, exporting only the constraint; a generic theorem proved from
; the constraint alone; and its :functional-instance for a concrete function,
; whose obligation (the constraint, instantiated) ACL2 proves at the hint.
;
; Cited by ai/01-form-shapes.md, "encapsulate and :functional-instance".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((step-fn *) => *))                   ; signature: one argument, one value

  (local (defun step-fn (x) (nfix x)))   ; witness: local, so not exported

  (local (defthm step-fn-witness-lemma   ; a local helper, not exported
           (natp (nfix x))))

  (defthm natp-of-step-fn                ; the constraint: exported
    (natp (step-fn x))
    :rule-classes :type-prescription))

; Only the constraint is known: the witness's definition is gone.
(local (must-fail (thm (equal (step-fn 3) 3))))
(assert-event (not (getpropc 'step-fn-witness-lemma 'theorem nil (w state))))

; A generic function over the constrained one, and a theorem about it.
(defun run-steps (xs)
  (if (consp xs)
      (+ (step-fn (car xs)) (run-steps (cdr xs)))
    0))

; The generic theorem needs an induction, done once, here.
(defthm run-steps-of-append
  (equal (run-steps (append a b))
         (+ (run-steps a) (run-steps b))))

; A concrete instance.  The definitions must have the same shape for the
; functional substitution to map RUN-STEPS onto RUN-LENS.
(defun len-fn (x) (len x))

(defun run-lens (xs)
  (if (consp xs)
      (+ (len-fn (car xs)) (run-lens (cdr xs)))
    0))

; Without induction the concrete theorem is refused ...
(local
 (must-fail
  (thm (equal (run-lens (append a b)) (+ (run-lens a) (run-lens b)))
       :hints (("Goal" :do-not-induct t)))))

; ... and with the functional instance it follows with no induction: ACL2
; proves the instantiated constraint, (NATP (LEN-FN X)), and the definition
; of RUN-STEPS with RUN-LENS and LEN-FN substituted.
(defthm run-lens-of-append
  (equal (run-lens (append a b)) (+ (run-lens a) (run-lens b)))
  :hints (("Goal" :do-not-induct t
                  :use ((:functional-instance run-steps-of-append
                                              (step-fn len-fn)
                                              (run-steps run-lens))))))
