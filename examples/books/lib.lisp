; examples/books/lib.lisp
;
; What it shows: a library book with a LOCAL lemma, a LOCAL include-book, and
; an explicit export theory at the end.  Everything local is used to certify
; the book and is absent from any world that includes it; the export event
; decides which of the book's own rules an includer gets enabled.  The
; includer is examples/books/user.lisp.
;
; Cited by humans/02-rewriting-theories-books.md, "local and the export
; boundary" and "Books and certification".

(in-package "ACL2")

; A local include: its rules help prove this book's theorems, and nothing of
; it reaches an includer.  It is not part of this book's interface.
(local (include-book "std/lists/take" :dir :system))

(defun sum-list (x)
  (if (consp x)
      (+ (fix (car x)) (sum-list (cdr x)))
    0))

; A local lemma: proof vocabulary, not interface.
(local
 (defthm sum-list-of-append-local
   (equal (sum-list (append x y))
          (+ (sum-list x) (sum-list y)))))

; The exported fact, proved with the local lemma.
(defthm sum-list-of-append-of-cons
  (equal (sum-list (append x (cons a y)))
         (+ (sum-list x) (fix a) (sum-list y))))

; Proved with the locally included TAKE rules (LEN-OF-TAKE).
(defthm len-of-take-of-sum-list-input
  (equal (len (take (len x) x)) (len x)))

; Export theory: withdraw the definition so includers reason with the
; exported lemma rather than by opening SUM-LIST.  fn ends every book with an
; explicit theory event like this one (fn docs/proof-style.md section 2).
(deftheory lib-internals
  '((:d sum-list) (:i sum-list)))

(in-theory (disable lib-internals))
