; examples/stobjs/attach-mem-logic.lisp
;
; The logical side shared by the two memory stobjs of
; examples/stobjs/attach-stobj.lisp: a list of *mem-len* values, read with
; NTH and written with UPDATE-NTH.  (books/demos/attach-stobj/logic.lisp has
; the same role.)
;
; Cited by humans/03-modelling-data.md, "Attachable stobjs".

(in-package "ACL2")

(defconst *mem-len* 64)

; ---------------------------------------------------------------------------
; The logical side, shared by both stobjs.

(defun mem$ap (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) *mem-len*)))

(defun create-mem$a ()
  (declare (xargs :guard t))
  (make-list *mem-len*))

(defun mem-indexp (n)
  (declare (xargs :guard t))
  (and (natp n) (< n *mem-len*)))

(defun lookup$a (n x)
  (declare (xargs :guard (and (mem-indexp n) (mem$ap x))))
  (nth n x))

(defun update$a (n v x)
  (declare (xargs :guard (and (mem-indexp n) (mem$ap x))))
  (update-nth n v x))

