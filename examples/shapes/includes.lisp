; examples/shapes/includes.lisp
;
; Shapes: include-book of a community book with :dir :system (exported to
; every includer), a LOCAL include (a private tool: its rules help this
; book's proofs and are not exported), a relative include of a sibling book,
; and an export theory event at the end.  includes-user.lisp includes this
; book and checks what arrived.
;
; Cited by ai/01-form-shapes.md, "include-book".

(in-package "ACL2")

(include-book "std/lists/rev" :dir :system)            ; exported
(local (include-book "std/lists/take" :dir :system))   ; private
(include-book "teeth")                                  ; a sibling, by relative name

; Proved here with LEN-OF-TAKE from the local include.
(defthm len-of-take-of-rev
  (implies (natp n)
           (equal (len (take n (rev x))) n)))

(defund rev-twice (x) (rev (rev x)))

; Export event: what leaves this book enabled is a decision, made last.
(in-theory (disable len-of-take-of-rev))
