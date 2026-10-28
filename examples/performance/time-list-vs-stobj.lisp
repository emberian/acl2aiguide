; acl2aiguide example (a test book): time$ measurements of a list
; representation against a stobj array, and of with-local-stobj per call.
;
; Cited by humans/05-high-performance.md, sections "Finding the consing" and
; "The representation lesson".  The numbers are printed by time$ while the
; book certifies; the record is this book's .cert.out, and the chapter quotes
; them as [measured: ...] with the command that produced them.
;
; What it shows:
;   - a list of N words costs 16 bytes of allocation per element to build,
;     the stobj array costs nothing after it exists (the stobj itself is
;     allocated once, by with-local-stobj's creator: 8 bytes per word);
;   - a sequential scan over either allocates nothing and takes about the
;     same time; the difference is the build, and access by index (nth walks
;     the list, the array reads one word);
;   - with-local-stobj allocates its stobj on EVERY call, so a scratch stobj
;     made per call is per-call allocation, and threading one stobj through
;     the loop is not;
;   - the proof-side pitfall of a large stobj: its creator's definition is a
;     list of N elements, and a draft whose guard conjecture was
;     (< 5 (V-LENGTH (VEC-FILL 0 (CREATE-VEC)))) ran for more than four
;     minutes without finishing (chapter 5, section 5.2), so here the
;     creator's definition is disabled after the one fact the guards need.
;
; The stobjs are :non-executable t: no global copy is allocated, because this
; book only ever uses them through with-local-stobj (:DOC defstobj,
; "Specifying Non-executable Stobjs").

(in-package "ACL2")

(defconst *n* 1000000)

(defstobj vec
  (v :type (array (unsigned-byte 61) (*n*)) :initially 0 :resizable nil)
  :inline t :non-executable t)

(defthm vecp-of-create-vec (vecp (create-vec)))
(in-theory (disable create-vec))

(defthm vp-of-update-nth
  (implies (and (vp l) (natp i) (< i (len l)) (unsigned-byte-p 61 x))
           (vp (update-nth i x l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm vec-len-of-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (len (update-nth i x l)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm vp-nth-natp
  (implies (and (vp l) (natp i) (< i (len l))) (natp (nth i l)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nth))))

(defthm vp-nth-below
  (implies (and (vp l) (natp i) (< i (len l))) (< (nth i l) (expt 2 61)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nth))))

; ---------------------------------------------------------------------------
; The stobj side.

(defun vec-fill (i vec)
  (declare (xargs :stobjs vec :guard (and (natp i) (<= i *n*))
                  :measure (nfix (- *n* (nfix i))))
           (type (integer 0 1000000) i))
  (if (mbe :logic (or (not (natp i)) (>= i *n*)) :exec (= i *n*))
      vec
    (let ((vec (update-vi i i vec)))
      (vec-fill (the (integer 0 1000000) (+ 1 i)) vec))))

(defthm vecp-of-vec-fill
  (implies (vecp vec) (vecp (vec-fill i vec))))

(defun vec-count (x i acc vec)
  (declare (xargs :stobjs vec
                  :guard (and (natp i) (natp acc) (<= i *n*) (<= acc i))
                  :measure (nfix (- *n* (nfix i))))
           (type (unsigned-byte 61) x)
           (type (integer 0 1000000) i acc))
  (if (mbe :logic (or (not (natp i)) (>= i *n*)) :exec (= i *n*))
      acc
    (vec-count x
               (the (integer 0 1000000) (+ 1 i))
               (if (= x (the (unsigned-byte 61) (vi i vec)))
                   (the (integer 0 1000000) (+ 1 acc))
                 acc)
               vec)))

(defun vec-count-k (k vec)
  (declare (xargs :stobjs vec :guard (natp k)))
  (if (zp k)
      0
    (let ((c (vec-count 7 0 0 vec)))
      (if (= k 1) c (vec-count-k (- k 1) vec)))))

; K reads of the last word, by index.
(defun vec-last-k (k acc vec)
  (declare (xargs :stobjs vec
                  :guard (and (natp k) (natp acc))))
  (if (zp k)
      acc
    (vec-last-k (- k 1) (max acc (vi (- *n* 1) vec)) vec)))

(defun bench-stobj ()
  (declare (xargs :guard t))
  (time$
   (with-local-stobj vec
     (mv-let (r vec)
       (let ((vec (time$ (vec-fill 0 vec)
                         :mintime 0
                         :msg "stobj: fill 1,000,000 words: ~sa bytes, ~st s~%")))
         (mv (list (time$ (vec-count-k 100 vec)
                          :mintime 0
                          :msg "stobj: 100 scans of 1,000,000 words: ~sa bytes, ~st s~%")
                   (time$ (vec-last-k 100 0 vec)
                          :mintime 0
                          :msg "stobj: 100 reads of word 999,999 by index: ~sa bytes, ~st s~%"))
             vec))
       r))
   :mintime 0
   :msg "stobj: whole with-local-stobj form (creator included): ~sa bytes, ~st s~%"))

; ---------------------------------------------------------------------------
; The list side: the same words, the same count.

(defun words-below (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (words-below (- n 1) (cons (- n 1) acc))))

(defun list-count (x l acc)
  (declare (xargs :guard (and (true-listp l) (natp acc))))
  (cond ((endp l) acc)
        ((equal x (car l)) (list-count x (cdr l) (+ 1 acc)))
        (t (list-count x (cdr l) acc))))

(defun list-count-k (k l)
  (declare (xargs :guard (and (natp k) (true-listp l))))
  (if (zp k)
      0
    (let ((c (list-count 7 l 0)))
      (if (= k 1) c (list-count-k (- k 1) l)))))

(defthm true-listp-of-words-below
  (implies (true-listp acc) (true-listp (words-below n acc))))

(defun list-last-k (k acc l)
  (declare (xargs :guard (and (natp k) (natp acc) (nat-listp l))))
  (if (zp k)
      acc
    (list-last-k (- k 1) (max acc (nfix (nth (- *n* 1) l))) l)))

(defthm nat-listp-of-words-below
  (implies (nat-listp acc) (nat-listp (words-below n acc))))

(defun bench-list ()
  (declare (xargs :guard t))
  (let ((l (time$ (words-below *n* nil)
                  :mintime 0
                  :msg "list: build 1,000,000 words: ~sa bytes, ~st s~%")))
    (list (time$ (list-count-k 100 l)
                 :mintime 0
                 :msg "list: 100 scans of 1,000,000 words: ~sa bytes, ~st s~%")
          (time$ (list-last-k 100 0 l)
                 :mintime 0
                 :msg "list: 100 reads of word 999,999 by nth: ~sa bytes, ~st s~%"))))

; ---------------------------------------------------------------------------
; Scratch space: a with-local-stobj per call, against one threaded stobj.

(defstobj scratch
  (s :type (array (unsigned-byte 61) (2048)) :initially 0 :resizable nil)
  :inline t :non-executable t)

(defthm scratchp-of-create-scratch (scratchp (create-scratch)))
(in-theory (disable create-scratch))

(defthm sp-of-update-nth
  (implies (and (sp l) (natp i) (< i (len l)) (unsigned-byte-p 61 x))
           (sp (update-nth i x l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm sp-nth-natp
  (implies (and (sp l) (natp i) (< i (len l))) (natp (nth i l)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nth))))

(defthm sp-nth-below
  (implies (and (sp l) (natp i) (< i (len l))) (< (nth i l) (expt 2 61)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nth))))

; One call, one fresh stobj.
(defun scratch-per-call (x)
  (declare (xargs :guard (unsigned-byte-p 61 x)))
  (with-local-stobj scratch
    (mv-let (r scratch)
      (let ((scratch (update-si 0 x scratch)))
        (mv (si 0 scratch) scratch))
      r)))

(defun scratch-per-call-k (k acc)
  (declare (xargs :guard (and (natp k) (< k 1000000) (natp acc))))
  (if (zp k)
      acc
    (scratch-per-call-k (- k 1) (+ acc (scratch-per-call k)))))

; One stobj for the whole loop.
(defun scratch-threaded-k (k acc scratch)
  (declare (xargs :stobjs scratch
                  :guard (and (natp k) (< k 1000000) (natp acc))))
  (if (zp k)
      (mv acc scratch)
    (let ((scratch (update-si 0 k scratch)))
      (scratch-threaded-k (- k 1) (+ acc (si 0 scratch)) scratch))))

(defun bench-scratch ()
  (declare (xargs :guard t))
  (list (time$ (scratch-per-call-k 1000 0)
               :mintime 0
               :msg "scratch: 1000 calls, one with-local-stobj each: ~sa bytes, ~st s~%")
        (time$ (with-local-stobj scratch
                 (mv-let (r scratch)
                   (scratch-threaded-k 1000 0 scratch)
                   r))
               :mintime 0
               :msg "scratch: 1000 steps over one with-local-stobj: ~sa bytes, ~st s~%")))

; ---------------------------------------------------------------------------
; Run them while certifying.  The answers are checked; the timings are printed.

(assert-event (equal (bench-stobj) (list 1 999999)))
(assert-event (equal (bench-list) (list 1 999999)))
(assert-event (equal (bench-scratch) (list 500500 500500)))
