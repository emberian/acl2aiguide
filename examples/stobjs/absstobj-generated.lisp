; examples/stobjs/absstobj-generated.lisp
;
; A bounded set of naturals below 16 as an abstract stobj, with its
; obligations GENERATED: a make-event asks ACL2 for the missing events
; (defabsstobj-missing-events, given the same arguments as the defabsstobj)
; and admits each as a :rule-classes nil defthm closed by one uniform hint.
; This is the shape fn's generators use (fn books/proto/adt.lisp,
; adt-obligation-thms; books/def-representation.lisp).  The correspondence
; is stated once; the content is in three lemmas about it.
;
; Cited by humans/03-modelling-data.md, "Abstract stobjs" (generating the
; obligations).

(in-package "ACL2")

(defconst *bset-n* 16)

; Foundation: one bit per element and a cardinality cell.
(defstobj bset$c
  (bits :type (array bit (*bset-n*)) :initially 0)
  (cnt :type (integer 0 *) :initially 0))

; Logical side: a duplicate-free list of naturals below 16.
(defun below-n-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (natp (car x)) (< (car x) *bset-n*) (below-n-listp (cdr x)))))

(defun bset$ap (x)
  (declare (xargs :guard t))
  (and (below-n-listp x) (no-duplicatesp-equal x)))

(defun create-bset$a () (declare (xargs :guard t)) nil)

(defun bset$a-mem (k x)
  (declare (xargs :guard (and (natp k) (< k *bset-n*) (bset$ap x))))
  (if (member-equal k x) t nil))

(defun bset$a-insert (k x)
  (declare (xargs :guard (and (natp k) (< k *bset-n*) (bset$ap x))))
  (if (member-equal k x) x (cons k x)))

(defun bset$a-card (x)
  (declare (xargs :guard (bset$ap x)))
  (len x))

; Executables over the foundation.
(defun bset$c-mem (k bset$c)
  (declare (xargs :stobjs bset$c :guard (and (natp k) (< k *bset-n*))))
  (equal (bitsi k bset$c) 1))

(defun bset$c-insert (k bset$c)
  (declare (xargs :stobjs bset$c :guard (and (natp k) (< k *bset-n*))))
  (if (equal (bitsi k bset$c) 1)
      bset$c
    (let ((bset$c (update-bitsi k 1 bset$c)))
      (update-cnt (+ 1 (cnt bset$c)) bset$c))))

; The correspondence: every bit at or above I says membership, and the
; count is the length.
(defun bits-match (i bits x)
  (declare (xargs :measure (nfix (- *bset-n* i))))
  (if (or (not (natp i)) (>= i *bset-n*))
      t
    (and (iff (equal (nth i bits) 1) (member-equal i x))
         (bits-match (+ 1 i) bits x))))

(defun-nx bset$corr (bset$c x)
  (and (bits-match 0 (nth 0 bset$c) x)
       (equal (nth 1 bset$c) (len x))))

; The content: a read through the match, and the match after an insert.
(defthm bits-match-reads
  (implies (and (bits-match i bits x) (natp i) (natp k) (<= i k) (< k *bset-n*))
           (iff (equal (nth k bits) 1) (member-equal k x))))

(defthm bits-match-of-insert
  (implies (and (bits-match i bits x) (natp k) (< k *bset-n*))
           (bits-match i (update-nth k 1 bits) (cons k x))))

; Close the correspondence's recursion: the obligations are to be closed by
; the two lemmas, not by re-opening BITS-MATCH (which, open, unrolls at 0
; and leaves a checkpoint about (BITS-MATCH 1 ...)).
(in-theory (disable bits-match))

; The defabsstobj form, written once as a constant so that the generator and
; the event cannot drift apart.
(defconst *bset-defabsstobj*
  '(defabsstobj bset
     :foundation bset$c
     :recognizer (bsetp :logic bset$ap :exec bset$cp)
     :creator (create-bset :logic create-bset$a :exec create-bset$c)
     :corr-fn bset$corr
     :exports ((bset-mem :logic bset$a-mem :exec bset$c-mem)
               (bset-insert :logic bset$a-insert :exec bset$c-insert :protect t)
               (bset-card :logic bset$a-card :exec cnt))))

; The generator: one defthm per missing event, one hint for all of them.
(defun bset-obligation-thms (missing hints wrld)
  (declare (xargs :mode :program))
  (if (endp missing)
      nil
    (cons `(defthm ,(car (car missing))
             ,(untranslate (cadr (car missing)) t wrld)
             :rule-classes nil
             :hints ,hints)
          (bset-obligation-thms (cdr missing) hints wrld))))

; DEFABSSTOBJ-MISSING-EVENTS is a macro taking the defabsstobj's own
; arguments, so the outer make-event splices them in from the constant and
; the inner one runs it.  Its value is a list of (NAME FORMULA . OLD), the
; formula translated (:DOC defabsstobj-missing-events).
(make-event
 `(make-event
   (er-let* ((missing (defabsstobj-missing-events ,@(cdr *bset-defabsstobj*))))
     (value (cons 'progn
                  (bset-obligation-thms
                   missing
                   '(("Goal" :in-theory (enable bset$corr bset$ap bset$a-mem
                                                bset$a-insert bset$a-card
                                                bset$c-mem bset$c-insert)))
                   (w state)))))))

(make-event *bset-defabsstobj*)

; Theorems over the logical list.
(defthm bset-mem-of-bset-insert
  (implies (and (natp k) (< k *bset-n*))
           (bset-mem k (bset-insert k s))))

(defthm bset-card-of-bset-insert-new
  (implies (not (bset-mem k s))
           (equal (bset-card (bset-insert k s)) (+ 1 (bset-card s)))))

(defun insert-all (ks bset)
  (declare (xargs :stobjs bset :guard (below-n-listp ks)))
  (if (atom ks)
      bset
    (let ((bset (bset-insert (car ks) bset)))
      (insert-all (cdr ks) bset))))

(defun distinct-count (ks)
  (declare (xargs :guard (below-n-listp ks)))
  (with-local-stobj
   bset
   (mv-let (n bset)
     (let ((bset (insert-all ks bset)))
       (mv (bset-card bset) bset))
     n)))

(assert-event (equal (distinct-count '(3 1 3 7 1 15)) 4))
