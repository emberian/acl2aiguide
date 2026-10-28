; examples/shapes/mbe-memoize.lisp
;
; Shapes: an mbe loop twin -- a recursive :logic body for proofs, a
; tail-recursive accumulator loop as :exec -- with the bridge theorem the
; guard proof needs, stated :rule-classes nil and given by :use in
; :guard-hints; and memoize on a guard-verified function.
;
; Cited by ai/01-form-shapes.md, "mbe" and "memoize".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; The logical definition: what theorems are about.
(defun sum-to (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (+ n (sum-to (- n 1)))))

; The loop: what runs.
(defun sum-to-loop (n acc)
  (declare (xargs :guard (and (natp n) (natp acc))))
  (if (zp n) acc (sum-to-loop (- n 1) (+ n acc))))

; The bridge, general in ACC so that it proves by induction.
(defthm sum-to-loop-is-sum-to
  (implies (natp acc)
           (equal (sum-to-loop n acc) (+ acc (sum-to n))))
  :rule-classes nil)

; The twin: :logic is the recursion, :exec the loop.  The guard proof of an
; mbe includes (EQUAL exec logic); the bridge discharges it.
(defun sum-to-fast (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :use ((:instance sum-to-loop-is-sum-to
                                                         (acc 0)))))))
  (mbe :logic (sum-to n)
       :exec (sum-to-loop n 0)))

; Without the bridge the guard proof is refused.
(local
 (must-fail
  (defun sum-to-fast-bad (n)
    (declare (xargs :guard (natp n)
                    :guard-hints (("Goal" :do-not-induct t))))
    (mbe :logic (sum-to n)
         :exec (sum-to-loop n 0)))))

; Theorems see only the :logic side.
(defthm sum-to-fast-is-sum-to
  (equal (sum-to-fast n) (sum-to n)))

(assert-event (equal (sum-to-fast 100000) 5000050000))
(assert-event (eq (symbol-class 'sum-to-fast (w state)) :common-lisp-compliant))

; memoize: remember results of a guard-verified function's raw Lisp calls.
(defun fib (n)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (= n 1))
      1
    (+ (fib (- n 1)) (fib (- n 2)))))

(memoize 'fib)

(assert-event (equal (fib 80) 37889062373143906))
