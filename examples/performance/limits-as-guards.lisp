; acl2aiguide example: a defconst-bounded limits table used as guards, a
; bounded loop with a measure, and the entry check that refuses once so the
; loop never checks again.
;
; Cited by humans/05-high-performance.md, section "TigerStyle in ACL2"
; ("put a limit on everything", "assert the relationships of compile-time
; constants", explicitly sized types).
;
; What it shows:
;   - every limit is a defconst, and the relations between limits (the batch
;     ceiling is records times line length; the ceiling is a fixnum) are
;     assert-events, checked when the book certifies;
;   - the limits table is read through a MACRO, so the term a book admits is
;     the literal number and no proof or execution sees a lookup (the shape of
;     fn's fn-proto-text, books/protocol-table.lisp);
;   - the loop's accumulator is declared (unsigned-byte 60) and every sum is
;     wrapped in `the'; the guard carries exactly the arithmetic fact that
;     makes the declaration true (acc plus the rest's worst case fits);
;   - the entry point admits a batch or refuses it with a typed word, and the
;     ceiling on its answer is a theorem.

(in-package "ACL2")

(defconst *line-octets-max* 512)
(defconst *batch-records-max* 64)
(defconst *batch-octets-max* (* *batch-records-max* *line-octets-max*))

(defconst *limits*
  `((:line-octets   . ,*line-octets-max*)
    (:batch-records . ,*batch-records-max*)
    (:batch-octets  . ,*batch-octets-max*)))

; Relations between the limits, checked at certification.
(assert-event (equal *batch-octets-max* (* *batch-records-max* *line-octets-max*)))
(assert-event (< *batch-octets-max* (expt 2 60)))
(assert-event (posp *line-octets-max*))

; A limit by name, expanded at macroexpansion time to its number.
(defmacro limit (name)
  (let ((pair (assoc-eq name *limits*)))
    (if (consp pair)
        (cdr pair)
      (er hard 'limit "No limit named ~x0 in *limits*." name))))

(assert-event (equal (limit :batch-octets) 32768))

; A batch is a list of line lengths, each within the line limit.
(defun bounded-nat-listp (l max)
  (declare (xargs :guard (natp max)))
  (if (atom l)
      (null l)
    (and (natp (car l))
         (<= (car l) max)
         (bounded-nat-listp (cdr l) max))))

; The loop.  Its guard says the accumulator plus the worst case of what is
; left still fits the batch ceiling, which is what the `the' needs.
(defun batch-octets-loop (l acc)
  (declare (xargs :guard (and (bounded-nat-listp l (limit :line-octets))
                              (natp acc)
                              (<= (+ acc (* (len l) (limit :line-octets)))
                                  (limit :batch-octets)))
                  :measure (len l))
           (type (unsigned-byte 60) acc))
  (if (endp l)
      acc
    (batch-octets-loop (cdr l) (the (unsigned-byte 60) (+ (car l) acc)))))

(defun batch-octets-spec (l)
  (declare (xargs :guard (true-listp l)))
  (if (endp l) 0 (+ (nfix (car l)) (batch-octets-spec (cdr l)))))

(defthm batch-octets-loop-is-spec
  (implies (and (bounded-nat-listp l max) (natp acc))
           (equal (batch-octets-loop l acc)
                  (+ acc (batch-octets-spec l)))))

(defthm batch-octets-spec-bound
  (implies (and (bounded-nat-listp l max) (natp max))
           (<= (batch-octets-spec l) (* (len l) max)))
  :rule-classes :linear)

; The entry: the limits are checked here, once, and refused by name.
(defun admit-batch (l)
  (declare (xargs :guard t))
  (cond ((not (bounded-nat-listp l (limit :line-octets)))
         (mv :line-over-limit 0))
        ((> (len l) (limit :batch-records))
         (mv :batch-over-limit 0))
        (t (mv :ok (batch-octets-loop l 0)))))

(defthm admit-batch-answer-is-within-the-ceiling
  (<= (mv-nth 1 (admit-batch l)) (limit :batch-octets))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance batch-octets-spec-bound
                                   (max (limit :line-octets)))))))

(defthm admit-batch-word
  (member-eq (mv-nth 0 (admit-batch l))
             '(:ok :line-over-limit :batch-over-limit)))

; Witnesses for each answer.
; (An assert-event checks one value, so a two-valued answer is read with
; mv-list.)
(assert-event (equal (mv-list 2 (admit-batch '(10 20 30))) '(:ok 60)))
(assert-event (equal (mv-list 2 (admit-batch '(10 513))) '(:line-over-limit 0)))
(assert-event (equal (mv-list 2 (admit-batch (make-list 65 :initial-element 1)))
                     '(:batch-over-limit 0)))
(assert-event (equal (mv-list 2 (admit-batch (make-list 64 :initial-element 512)))
                     '(:ok 32768)))
