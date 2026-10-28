; examples/modelling/mbe-loop-twin.lisp
;
; The loop twin: the :logic body of an mbe is the structural recursion the
; rewriter sees and every theorem is about; the :exec body is an accumulator
; loop that runs in constant stack; one bridge lemma relates them, and the
; guard verification of the wrapper is where the mbe equality obligation is
; discharged (:DOC mbe: the guard obligations of an mbe include
; (equal exec-code logic-code)).  This is the hand-written shape fn's
; def-loop generates (fn books/def-loop.lisp header).
;
; Cited by humans/03-modelling-data.md, "mbe and the loop twin".

(in-package "ACL2")

; The loop: tail recursive, accumulates in reverse.
(defun keep-evens-loop (xs acc)
  (declare (xargs :guard (and (integer-listp xs) (true-listp acc))))
  (if (consp xs)
      (keep-evens-loop (cdr xs)
                       (if (evenp (car xs)) (cons (car xs) acc) acc))
    (revappend acc nil)))

; The function: logically the structural recursion, executed by the loop.
(defun keep-evens (xs)
  (declare (xargs :guard (integer-listp xs) :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (if (evenp (car xs))
                      (cons (car xs) (keep-evens (cdr xs)))
                    (keep-evens (cdr xs)))
                nil)
       :exec (keep-evens-loop xs nil)))

; The bridge: the loop is revappend of the accumulator onto the recursion.
; It is stated for every ACC, which is what makes the induction go through.
(defthm keep-evens-loop-is-revappend
  (equal (keep-evens-loop xs acc)
         (revappend acc (keep-evens xs))))

; The mbe obligation is (equal (keep-evens-loop xs nil) <logic body>); the
; bridge at ACC = nil closes it.
(verify-guards keep-evens)

; Every theorem is about the recursion; none mentions the loop.
(defthm integer-listp-of-keep-evens
  (implies (integer-listp xs) (integer-listp (keep-evens xs))))

(defthm keep-evens-of-append
  (equal (keep-evens (append xs ys))
         (append (keep-evens xs) (keep-evens ys))))

(in-theory (disable keep-evens-loop))

; On a long list the guard-verified wrapper runs the loop in raw Lisp.
(defun range-list (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (range-list (- n 1) (cons n acc))))

(assert-event
 (equal (len (keep-evens (range-list 1000000 nil))) 500000))
