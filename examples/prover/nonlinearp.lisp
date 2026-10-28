; examples/prover/nonlinearp.lisp
;
; What it shows: a product inequality that linear arithmetic cannot prove
; (it treats (* x y) as an unknown), and the :nonlinearp hint, which lets the
; arithmetic procedure multiply known inequalities together
; (:doc non-linear-arithmetic).
;
; Cited by humans/01-logic-and-prover.md, "The hints: :nonlinearp".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(local
 (must-fail
  (thm (implies (and (rationalp x) (rationalp y) (< 1 x) (< 1 y))
                (< 1 (* x y))))))

(defthm product-of-two-above-one
  (implies (and (rationalp x) (rationalp y) (< 1 x) (< 1 y))
           (< 1 (* x y)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)
