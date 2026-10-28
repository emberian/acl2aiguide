; examples/books/make-event-check.lisp
;
; What it shows: make-event computes an event at certification time from the
; state and the world; its expansion is stored in the certificate and re-used,
; not recomputed, by include-book (:doc make-event).  Here it refuses to
; certify the book unless a check holds, and records a computed constant.
; assert-event is the one-line form of the same idea (:doc assert-event).
;
; Cited by humans/02-rewriting-theories-books.md, "make-event, assert-event".

(in-package "ACL2")

(defun rv (x)
  (if (consp x) (append (rv (cdr x)) (list (car x))) nil))

; A certification-time check written as make-event: the expansion is a
; harmless event when the check holds, and an error otherwise.
(make-event
 (if (equal (rv '(a b c)) '(c b a))
     '(value-triple :rv-check-passed)
   (er soft 'rv-check "RV does not reverse '(a b c).")))

; The same check as assert-event.
(assert-event (equal (rv '(a b c)) '(c b a)))

; A constant computed from the world at certification time.  An includer gets
; the value recorded then (the stored expansion), whatever its own world is.
(make-event
 `(defconst *rv-book-world-length-at-cert* ,(length (w state))))

(assert-event (posp *rv-book-world-length-at-cert*))
