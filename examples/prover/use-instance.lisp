; examples/prover/use-instance.lisp
;
; What it shows: a :use hint with :instance, and its classic pitfall.  :use
; adds the instantiated formula as a HYPOTHESIS of the goal; if the lemma is
; also an enabled rewrite rule, the rewriter simplifies the new hypothesis to T
; and it is gone.  Disabling the lemma in the same hint fixes it.  (This is the
; example of :doc using-enabled-rules.)
;
; Cited by humans/01-logic-and-prover.md, "The hints: :use".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun p (x) (cons x x))

(defthm car-p
  (equal (car (p x)) x))

(in-theory (disable p (:type-prescription p)))

; Both instances are added as hypotheses and both rewrite to T by CAR-P, so the
; goal is left without them.  ACL2 prints a [Use] warning saying exactly this.
(local
 (must-fail
  (thm (implies (equal (p x1) (p x2))
                (equal x1 x2))
       :hints (("Goal" :use ((:instance car-p (x x1))
                             (:instance car-p (x x2))))))))

; The repair: keep the hypotheses by disabling the rule they came from.
(defthm p-injective
  (implies (equal (p x1) (p x2))
           (equal x1 x2))
  :hints (("Goal" :use ((:instance car-p (x x1))
                        (:instance car-p (x x2)))
                  :in-theory (disable car-p)))
  :rule-classes nil)
