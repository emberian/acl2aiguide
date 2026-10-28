; examples/fn-lessons/list-view-nonexec.lisp
;
; What it shows: a list view of a payload kept for the logic only.  The view
; is introduced by defun-nx with no guard, so its guards are never verified.
; A guard-verified definition that calls the view outside the :logic half of
; an mbe is then refused when it is admitted, so the executable path cannot
; quietly become a twin of the list path; the :exec half must be the real
; representation (here a string), and guard verification proves the two
; equal once (:doc defun-nx, :doc mbe, :doc verify-guards).
;
; Cited by fn-lessons/01-octet-lists-twins.md, "The shape to copy".

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun codes-of (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (codes-of (cdr chars)))
    nil))

(defthm len-of-codes-of
  (equal (len (codes-of chars)) (len chars)))

; The logical view: the payload's octets as a list.  No guard, so no guard
; verification; calls of it cannot be evaluated.
(defun-nx payload-octets (s)
  (codes-of (coerce s 'list)))

; The executable function: the logic is stated over the list view, the
; execution reads the string.
(defun payload-len (s)
  (declare (xargs :guard (stringp s)))
  (mbe :logic (len (payload-octets s))
       :exec (length s)))

(assert-event (equal (payload-len "abc") 3))

; A guard-verified function that walks the list view at run time is refused:
; "The body for PAYLOAD-LEN-BY-WALK calls the function PAYLOAD-OCTETS, the
; guards of which have not yet been verified."
(local
 (must-fail
  (defun payload-len-by-walk (s)
    (declare (xargs :guard (stringp s)))
    (len (payload-octets s)))))
