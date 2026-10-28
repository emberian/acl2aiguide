; examples/prover/by-and-restrict.lisp
;
; What it shows: two hints that point the prover at one rule instance.
; :by says the goal IS (is subsumed by) a known theorem, so no proof search is
; done; :restrict limits which instantiation of a free-variable rule the
; rewriter may try (the :doc hints example due to Mihir Mehta).
;
; Cited by humans/01-logic-and-prover.md, "The hints: :by, :restrict".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun drop (n x)
  (if (zp n) x (drop (1- n) (cdr x))))

(defthm drop-of-drop
  (implies (and (natp i) (natp j))
           (equal (drop i (drop j x))
                  (drop (+ i j) x))))

; The goal is DROP-OF-DROP with the variables renamed, so it is subsumed.
(defthm drop-of-drop-renamed
  (implies (and (natp a) (natp b))
           (equal (drop a (drop b y))
                  (drop (+ a b) y)))
  :hints (("Goal" :by drop-of-drop))
  :rule-classes nil)

; SUBSETP-TRANS has the free variable Y.  The rewriter finds no binding that
; makes both hypotheses true here and the proof fails.
(defthm subsetp-trans
  (implies (and (subsetp x y) (subsetp y z))
           (subsetp x z)))

(defthm subsetp-evens
  (subsetp-equal (evens l) l))

(local
 (must-fail
  (with-prover-step-limit 200000
    (thm (subsetp (evens (evens l)) l)))))

; :restrict says: when applying SUBSETP-TRANS, Y must be (evens l).
(defthm subsetp-evens-evens
  (subsetp (evens (evens l)) l)
  :hints (("Goal" :restrict ((subsetp-trans ((y (evens l))))))))
