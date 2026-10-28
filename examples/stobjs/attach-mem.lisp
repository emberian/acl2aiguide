; examples/stobjs/attach-mem.lisp
;
; The attachable abstract stobj MEM over an array foundation, its
; obligations proved against that foundation, and a theorem about it.
; Included by itself, MEM executes on the array; included after
; (attach-stobj mem mem-ht), it executes on MEM-HT's hash table and every
; theorem here is unchanged (examples/stobjs/attach-stobj.lisp).
; (books/demos/attach-stobj/mem.lisp has the same role.)
;
; Cited by humans/03-modelling-data.md, "Attachable stobjs".

(in-package "ACL2")
(include-book "attach-mem-logic")

; The attachable stobj's own foundation: an array.  Its obligations are
; proved against this foundation exactly as for any abstract stobj, even
; when an attachment means it is not what executes.

(defstobj mem$c (mem$c-ar :type (array t (*mem-len*))))

(defun-nx mem$corr (mem$c x)
  (equal x (nth 0 mem$c)))

(defun lookup$c (i mem$c)
  (declare (xargs :stobjs mem$c
                  :guard (and (natp i) (< i (mem$c-ar-length mem$c)))))
  (mem$c-ari i mem$c))

(defun update$c (i v mem$c)
  (declare (xargs :stobjs mem$c
                  :guard (and (natp i) (< i (mem$c-ar-length mem$c)))))
  (update-mem$c-ari i v mem$c))

(defthm create-mem{correspondence}
  (mem$corr (create-mem$c) (create-mem$a))
  :rule-classes nil)

(defthm create-mem{preserved}
  (mem$ap (create-mem$a))
  :rule-classes nil)

(defthm lookup{correspondence}
  (implies (and (mem$corr mem$c mem) (mem-indexp i) (mem$ap mem))
           (equal (lookup$c i mem$c) (lookup$a i mem)))
  :rule-classes nil)

(defthm lookup{guard-thm}
  (implies (and (mem$corr mem$c mem) (mem-indexp i) (mem$ap mem))
           (and (natp i) (< i (mem$c-ar-length mem$c))))
  :rule-classes nil)

(defthm update{correspondence}
  (implies (and (mem$corr mem$c mem) (mem-indexp i) (mem$ap mem))
           (mem$corr (update$c i v mem$c) (update$a i v mem)))
  :rule-classes nil)

(defthm update{guard-thm}
  (implies (and (mem$corr mem$c mem) (mem-indexp i) (mem$ap mem))
           (and (natp i) (< i (mem$c-ar-length mem$c))))
  :rule-classes nil)

(defthm update{preserved}
  (implies (and (mem-indexp i) (mem$ap mem))
           (mem$ap (update$a i v mem)))
  :rule-classes nil)

; Same :logic functions, export for export: the "corresponding logical
; skeletons" attach-stobj requires.
(defabsstobj mem
  :foundation mem$c
  :recognizer (memp :logic mem$ap :exec mem$cp)
  :creator (create-mem :logic create-mem$a :exec create-mem$c)
  :corr-fn mem$corr
  :exports ((lookup :logic lookup$a :exec lookup$c)
            (update :logic update$a :exec update$c))
  :attachable t)


; Theorems about MEM are proved once, about the logic.
(defthm lookup-update
  (implies (and (mem-indexp i) (mem-indexp j))
           (equal (lookup i (update j v mem))
                  (if (equal i j) v (lookup i mem)))))
