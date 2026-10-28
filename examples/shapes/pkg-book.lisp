; examples/shapes/pkg-book.lisp
;
; Shapes: a book in its own package.  The defpkg is NOT in the book (defpkg
; forms "should not occur in books", :doc defpkg); it is in pkg-book.acl2,
; which cert.pl runs first, and so it lands in the certificate's portcullis.
; The book starts with in-package of the new package.
;
; Cited by ai/01-form-shapes.md, "the .acl2 portcullis".

(in-package "SHAPES")

(defun double (x) (* 2 (fix x)))

(defthm double-of-double
  (equal (double (double x)) (* 4 (fix x))))

(assert-event (equal (symbol-package-name 'double) "SHAPES"))
