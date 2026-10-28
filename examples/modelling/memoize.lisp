; examples/modelling/memoize.lisp
;
; memoize on a pure, guard-verified function with a :condition: results are
; stored only for calls whose arguments satisfy the condition (:DOC
; memoize).  Memoization is a property of raw-Lisp execution; the logic and
; every theorem are unchanged by it.  A function that returns a stobj cannot
; be memoized.
;
; Cited by humans/03-modelling-data.md, "Memoization".

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (cond ((zp n) 0)
                    ((= n 1) 1)
                    (t (+ (fib (- n 1)) (fib (- n 2)))))
       :exec (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))

; Store results only for arguments above 10: small calls are cheaper to
; recompute than to look up.  The condition is a term over FIB's formals;
; ACL2 defines FIB-MEMOIZE-CONDITION from it and verifies its guards.
(memoize 'fib :condition '(> n 10))

; The recursion makes exponentially many calls; memoized, each N above 10
; is computed once.  Measured at the laptop REPL (ACL2 8.7, SBCL 2.6.8):
; (time$ (fib 32)) 0.06 s unmemoized, 0.00 s memoized; (fib 90) 0.00 s
; memoized.  The check below is evaluated at certification time.
(assert-event (equal (fib 90) 2880067194370816120))

; Memoization changes no theorem.
(defthm fib-of-2
  (equal (fib 2) 1))

(unmemoize 'fib)

; A function that returns a stobj cannot be memoized (:DOC memoize: "if it
; returns any stobjs").  The refusal reads: "Illegal attempt to set
; memoize-table:  SET-CELL returns a stobj, CELL (illegal except for
; profiling)." 
(defstobj cell fld)
(defun set-cell (v cell)
  (declare (xargs :stobjs cell))
  (update-fld v cell))
(must-fail (memoize 'set-cell))
