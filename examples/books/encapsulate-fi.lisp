; examples/books/encapsulate-fi.lisp
;
; What it shows: a constrained function introduced by encapsulate with a local
; witness, a generic theorem proved from its constraint alone, and two
; concrete theorems obtained from it by :functional-instance, each of which
; costs only the proof that the concrete functions satisfy the constraints
; (:doc encapsulate, :doc lemma-instance, :doc functional-instantiation-example).
;
; Cited by humans/02-rewriting-theories-books.md, "encapsulate, constrained
; functions, defattach".

(in-package "ACL2")

; OK is constrained to be Boolean and nothing else; the witness is local.
(encapsulate
  (((ok *) => *))
  (local (defun ok (x) (declare (ignore x)) t))
  (defthm booleanp-of-ok
    (booleanp (ok x))
    :rule-classes :type-prescription))

(defun all-ok (x)
  (if (atom x)
      (null x)
    (and (ok (car x))
         (all-ok (cdr x)))))

; The generic theorem: uses only what the encapsulate exported.
(defthm all-ok-of-append
  (implies (true-listp x)
           (equal (all-ok (append x y))
                  (and (all-ok x) (all-ok y)))))

; Instance 1: OK := INTEGERP, ALL-OK := INTEGER-LISTP.  The obligations are
; that INTEGERP is Boolean and that INTEGER-LISTP satisfies ALL-OK's
; definition with INTEGERP in place of OK.
(defthm integer-listp-of-append-fi
  (implies (true-listp x)
           (equal (integer-listp (append x y))
                  (and (integer-listp x) (integer-listp y))))
  :hints (("Goal" :use ((:functional-instance all-ok-of-append
                                              (ok integerp)
                                              (all-ok integer-listp))))))

; Instance 2: the same theorem for symbols, for the price of one hint.
(defthm symbol-listp-of-append-fi
  (implies (true-listp x)
           (equal (symbol-listp (append x y))
                  (and (symbol-listp x) (symbol-listp y))))
  :hints (("Goal" :use ((:functional-instance all-ok-of-append
                                              (ok symbolp)
                                              (all-ok symbol-listp))))))
