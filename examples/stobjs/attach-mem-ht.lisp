; examples/stobjs/attach-mem-ht.lisp
;
; The implementation stobj MEM-HT: the memory's logic over a hash-table
; foundation, with every defabsstobj obligation proved.  It is attached to
; MEM by examples/stobjs/attach-stobj.lisp.  (books/demos/attach-stobj/
; mem_ht.lisp has the same role.)
;
; Cited by humans/03-modelling-data.md, "Attachable stobjs".

(in-package "ACL2")
(include-book "attach-mem-logic")

; A hash table from address to value.

(defstobj mem-ht$c (mem-ht$c-tab :type (hash-table eql)))

; Every address below LEN reads, from the table, the list's element.
(defun list-alist-agree (i lst alist)
  (declare (xargs :measure (len lst)))
  (if (atom lst)
      t
    (and (equal (car lst) (cdr (hons-assoc-equal i alist)))
         (list-alist-agree (1+ i) (cdr lst) alist))))

(defun-nx mem-ht$corr (mem-ht$c x)
  (list-alist-agree 0 x (nth 0 mem-ht$c)))

(defun lookup-ht$c (k mem-ht$c)
  (declare (xargs :stobjs mem-ht$c :guard (eqlablep k)))
  (mem-ht$c-tab-get k mem-ht$c))

(defun update-ht$c (k v mem-ht$c)
  (declare (xargs :stobjs mem-ht$c :guard (eqlablep k)))
  (mem-ht$c-tab-put k v mem-ht$c))

(local
 (defthm list-alist-agree-nth-1
   (implies (and (natp i) (natp k) (< k (len lst))
                 (list-alist-agree i lst alist))
            (equal (nth k lst) (cdr (hons-assoc-equal (+ i k) alist))))
   :rule-classes nil))

(local
 (defthm list-alist-agree-nth
   (implies (and (natp k) (< k (len lst)) (list-alist-agree 0 lst alist))
            ; stated as an equality that is T, as books/demos/attach-stobj/
            ; mem_ht.lisp states it.  As a plain (EQUAL (CDR ...) (NTH K LST))
            ; the left side does not mention LST, so LST is a free variable
            ; the first hypothesis naming it, (< K (LEN LST)), must bind, and
            ; it does not: the obligation's checkpoint keeps the equality.
            (equal (equal (cdr (hons-assoc-equal k alist)) (nth k lst)) t))
   :hints (("Goal" :use ((:instance list-alist-agree-nth-1 (i 0)))))))

(local
 (defthm list-alist-agree-below
   (implies (and (integerp i) (natp n) (< n i)
                 (list-alist-agree i lst alist))
            (list-alist-agree i lst (cons (cons n v) alist)))))

(local
 (defun agree-update-induction (i lst alist k)
   (cond ((zp k) (list i lst alist k))
         ((atom lst) t)
         (t (agree-update-induction (1+ i) (cdr lst) alist (1- k))))))

(local
 (defthm list-alist-agree-update-1
   (implies (and (natp i) (list-alist-agree i lst alist)
                 (natp k) (< k (len lst)))
            (list-alist-agree i (update-nth k v lst)
                              (cons (cons (+ i k) v) alist)))
   :hints (("Goal" :induct (agree-update-induction i lst alist k)))
   :rule-classes nil))

(local
 (defthm list-alist-agree-update
   (implies (and (list-alist-agree 0 lst alist) (natp k) (< k (len lst)))
            (list-alist-agree 0 (update-nth k v lst) (cons (cons k v) alist)))
   :hints (("Goal" :use ((:instance list-alist-agree-update-1 (i 0)))))))

(defthm create-mem-ht{correspondence}
  (mem-ht$corr (create-mem-ht$c) (create-mem$a))
  :rule-classes nil)

(defthm create-mem-ht{preserved}
  (mem$ap (create-mem$a))
  :rule-classes nil)

(defthm lookup-ht{correspondence}
  (implies (and (mem-ht$corr mem-ht$c mem-ht) (mem-indexp k) (mem$ap mem-ht))
           (equal (lookup-ht$c k mem-ht$c) (lookup$a k mem-ht)))
  :hints (("Goal" :in-theory (disable hons-assoc-equal)))
  :rule-classes nil)

(defthm lookup-ht{guard-thm}
  (implies (and (mem-ht$corr mem-ht$c mem-ht) (mem-indexp k) (mem$ap mem-ht))
           (eqlablep k))
  :rule-classes nil)

(defthm update-ht{correspondence}
  (implies (and (mem-ht$corr mem-ht$c mem-ht) (mem-indexp k) (mem$ap mem-ht))
           (mem-ht$corr (update-ht$c k v mem-ht$c) (update$a k v mem-ht)))
  :rule-classes nil)

(defthm update-ht{guard-thm}
  (implies (and (mem-ht$corr mem-ht$c mem-ht) (mem-indexp k) (mem$ap mem-ht))
           (eqlablep k))
  :rule-classes nil)

(defthm update-ht{preserved}
  (implies (and (mem-indexp k) (mem$ap mem-ht))
           (mem$ap (update$a k v mem-ht)))
  :rule-classes nil)

; :non-executable t: this stobj exists only to be attached, so no global
; instance is allocated for it (the 2025 workshop abstract on attach-stobj).
(defabsstobj mem-ht
  :foundation mem-ht$c
  :recognizer (mem-htp :logic mem$ap :exec mem-ht$cp)
  :creator (create-mem-ht :logic create-mem$a :exec create-mem-ht$c)
  :corr-fn mem-ht$corr
  :exports ((lookup-ht :logic lookup$a :exec lookup-ht$c)
            (update-ht :logic update$a :exec update-ht$c))
  :non-executable t)

