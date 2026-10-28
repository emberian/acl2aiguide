; examples/shapes/stobj-fields.lisp
;
; Shapes: defstobj with a scalar field, a fixed array field (:resizable nil)
; and a hash-table field; the generated names (UPDATE-c, cI/UPDATE-cI,
; c-GET/c-PUT); the read-over-write theorems an includer needs, proved once
; over the generated definitions; and the element/update lemmas that a
; recognizer-preservation proof over an array write needs.
;
; Cited by ai/01-form-shapes.md, "defstobj".

(in-package "ACL2")

(defconst *slots* 16)

(defstobj st
  (cnt :type (integer 0 *) :initially 0)
  (arr :type (array (unsigned-byte 8) (*slots*)) :initially 0 :resizable nil)
  (tbl :type (hash-table equal) :initially nil))

; Element and update facts over the array field's recognizer.  A proof that
; a write preserves STP opens the recognizer into these NTH/UPDATE-NTH
; terms: without the three lemmas STP-OF-PUT-BYTE below is refused.
(defthm arrp-nth-natp
  (implies (and (arrp l) (natp i) (< i (len l)))
           (natp (nth i l)))
  :rule-classes :type-prescription)

(defthm arrp-nth-bound
  (implies (and (arrp l) (natp i) (< i (len l)))
           (< (nth i l) 256))
  :rule-classes :linear)

(defthm arrp-of-update-nth
  (implies (and (arrp l) (natp i) (< i (len l)) (unsigned-byte-p 8 v))
           (arrp (update-nth i v l))))

; Writers, guard-verified.
(defun bump (st)
  (declare (xargs :stobjs st))
  (update-cnt (+ 1 (cnt st)) st))

(defun put-byte (i v st)
  (declare (xargs :stobjs st
                  :guard (and (natp i) (< i *slots*) (unsigned-byte-p 8 v))))
  (update-arri i v st))

(defun remember (k v st)
  (declare (xargs :stobjs st))
  (tbl-put k v st))

; Read-over-write, stated in the accessor vocabulary.
(defthm arri-of-update-arri-same
  (equal (arri i (update-arri i v st)) v))

(defthm arri-of-update-arri-diff
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (arri i (update-arri j v st)) (arri i st))))

(defthm tbl-get-of-tbl-put-same
  (equal (tbl-get k (tbl-put k v st)) v))

(defthm cnt-of-update-arri
  (equal (cnt (update-arri i v st)) (cnt st)))

(defthm stp-of-put-byte
  (implies (and (stp st) (natp i) (< i *slots*) (unsigned-byte-p 8 v))
           (stp (put-byte i v st))))

; Then close the definitions, so includers reason in accessor vocabulary.
(in-theory (disable bump put-byte remember))

; Execution, through a local stobj (see local-stobj.lisp for its shape).
(defun demo ()
  (declare (xargs :guard t))
  (with-local-stobj st
    (mv-let (r st)
      (let* ((st (put-byte 3 7 st))
             (st (remember "key" 'val st))
             (st (bump st)))
        (mv (list (arri 3 st) (tbl-get "key" st) (cnt st) (arr-length st)) st))
      r)))

(assert-event (equal (demo) '(7 val 1 16)))
