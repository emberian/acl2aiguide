; examples/assured/square-paste.lisp
;
; What it shows: a correctness claim as a commuting square, proved once
; generically and paid for per transition kind (fn2's G1 squares and
; their vertical pasting, COHERENCE.md sections Notation and 2.1-2.2; the
; Lean form is Sq.paste_cover in fn2/meta/Fn2/Square.lean @dddc32d34).
;
; A square has two representations A and B, a relation SQ-REL between
; their states, a label interpretation SQ-H that sends each A label to a
; WORD of B labels (so the square may stutter: one fused A step stands for
; several B steps), and observations that the relation forces equal.
;
;   step:  (sq-rel a b) => (sq-rel (sq-a-step a l) (sq-b-run b (sq-h l)))
;   edge:  (sq-rel a b) => (equal (sq-a-obs a q) (sq-b-obs b q))
;   base:  (sq-rel (sq-a-init) (sq-b-init))
;
; SQ-PASTE (proved once, from the constraints alone) says the square for
; every label is a square for every word of labels; SQ-PASTE-OBS says the
; observations then agree after every run.  The instance below pays only
; for its step lemma per label kind and its edge lemma.
;
; The instance is a fused executor against a one-step-at-a-time
; reference, the shape of fn2's Q1 (fn2/books/reference.lisp @127f7b877):
;   A: per-connection byte counts plus a cached TOTAL; the fused label
;      (:recv2 k n m) takes two chunks for connection k in one step;
;   B: per-connection counts only; (:bump k n) adds one chunk; the total
;      is recomputed by the observation;
;   SQ-H sends (:recv2 k n m) to ((:bump k n) (:bump k m)).
; A teeth book cannot instantiate a wrong relation: the counter example at
; the end shows the cached total drifting when the fused step forgets the
; second chunk, and that the step obligation is false for that mutant.
;
; Cited by assured/humans/03-commuting-squares.md and
; assured/ai/03-commuting-squares.md.

(in-package "ACL2")

(encapsulate
  (((sq-a-init) => *) ((sq-b-init) => *)
   ((sq-a-step * *) => *) ((sq-b-step * *) => *)
   ((sq-h *) => *)
   ((sq-a-obs * *) => *) ((sq-b-obs * *) => *)
   ((sq-rel * *) => *))

  (local (defun sq-a-init () nil))
  (local (defun sq-b-init () nil))
  (local (defun sq-a-step (a l) (declare (ignore a l)) nil))
  (local (defun sq-b-step (b m) (declare (ignore b m)) nil))
  (local (defun sq-h (l) (declare (ignore l)) nil))
  (local (defun sq-a-obs (a q) (declare (ignore a q)) nil))
  (local (defun sq-b-obs (b q) (declare (ignore b q)) nil))
  (local (defun sq-rel (a b) (declare (ignore a b)) t))

  ; The reference run is defined inside, so the step constraint can say
  ; "the word the label stands for"; it is exported with its definition.
  (defun sq-b-run (b w)
    (if (atom w) b (sq-b-run (sq-b-step b (car w)) (cdr w))))

  (defthm sq-base (sq-rel (sq-a-init) (sq-b-init)))
  (defthm sq-step
    (implies (sq-rel a b)
             (sq-rel (sq-a-step a l) (sq-b-run b (sq-h l)))))
  (defthm sq-edge
    (implies (sq-rel a b)
             (equal (sq-a-obs a q) (sq-b-obs b q)))))

(defun sq-a-run (a w)
  (if (atom w) a (sq-a-run (sq-a-step a (car w)) (cdr w))))

; The reference word a concrete word stands for.
(defun sq-expand (w)
  (if (atom w) nil (append (sq-h (car w)) (sq-expand (cdr w)))))

(defthm sq-b-run-append
  (equal (sq-b-run b (append u v)) (sq-b-run (sq-b-run b u) v)))

(defun sq-paste-induct (a b w)
  (if (atom w) (list a b)
    (sq-paste-induct (sq-a-step a (car w)) (sq-b-run b (sq-h (car w))) (cdr w))))

(in-theory (disable (:executable-counterpart sq-a-run)
                    (:executable-counterpart sq-b-run)))

(defthm sq-paste
  (implies (sq-rel a b)
           (sq-rel (sq-a-run a w) (sq-b-run b (sq-expand w))))
  :hints (("Goal" :induct (sq-paste-induct a b w))))

(defthm sq-paste-obs
  (implies (sq-rel a b)
           (equal (sq-a-obs (sq-a-run a w) q)
                  (sq-b-obs (sq-b-run b (sq-expand w)) q)))
  :hints (("Goal" :use sq-paste :in-theory (disable sq-paste))))

; ----------------------------------------------------------------------
; The instance.  Connections 0..*conns*-1.

(include-book "std/lists/update-nth" :dir :system)

(defconst *conns* 4)

(defun countsp (xs)
  (if (atom xs) (null xs) (and (natp (car xs)) (countsp (cdr xs)))))

(defun sum-counts (xs) (if (atom xs) 0 (+ (nfix (car xs)) (sum-counts (cdr xs)))))

(defun bump (xs k n)
  (if (and (natp k) (< k (len xs)) (natp n))
      (update-nth k (+ n (nfix (nth k xs))) xs)
    xs))

; A: (counts . total).  B: counts.
(defun fused-init () (cons (make-list *conns* :initial-element 0) 0))
(defun ref-init () (make-list *conns* :initial-element 0))

(defun recv2-p (l)
  (and (true-listp l) (equal (len l) 4) (eq (car l) :recv2)
       (natp (cadr l)) (< (cadr l) *conns*) (natp (caddr l)) (natp (cadddr l))))

(defun fused-step (a l)
  (if (recv2-p l)
      (let ((k (cadr l)) (n (caddr l)) (m (cadddr l)))
        (cons (bump (car a) k (+ n m)) (+ (nfix (cdr a)) n m)))
    a))

(defun ref-step (b m)
  (if (and (true-listp m) (equal (len m) 3) (eq (car m) :bump))
      (bump b (cadr m) (caddr m))
    b))

(defun fused-h (l)
  (if (recv2-p l)
      (list (list :bump (cadr l) (caddr l)) (list :bump (cadr l) (cadddr l)))
    nil))

; Observations: (:total) or (:count k).
(defun fused-obs (a q)
  (if (equal q '(:total)) (cdr a) (nfix (nth (nfix (cadr q)) (car a)))))
(defun ref-obs (b q)
  (if (equal q '(:total)) (sum-counts b) (nfix (nth (nfix (cadr q)) b))))

; The relation: same counts, the cached total is their sum, and the
; counts have the declared shape.
(defun fused-rel (a b)
  (and (consp a) (countsp b) (equal (len b) *conns*)
       (equal (car a) b) (equal (cdr a) (sum-counts b))))

(defun ref-run (b w) (if (atom w) b (ref-run (ref-step b (car w)) (cdr w))))
(defun fused-run (a w) (if (atom w) a (fused-run (fused-step a (car w)) (cdr w))))
(defun fused-expand (w) (if (atom w) nil (append (fused-h (car w)) (fused-expand (cdr w)))))

; The per-label-kind lemmas: the instance's whole proof burden.
(defthm sum-counts-update-nth
  (implies (and (countsp xs) (natp k) (< k (len xs)) (natp v))
           (equal (sum-counts (update-nth k v xs))
                  (+ v (- (sum-counts xs) (nth k xs))))))

(defthm natp-nth-of-countsp
  (implies (and (countsp xs) (natp k) (< k (len xs)))
           (natp (nth k xs)))
  :rule-classes :type-prescription)

(defthm sum-counts-of-bump
  (implies (and (countsp xs) (natp k) (< k (len xs)) (natp n))
           (equal (sum-counts (bump xs k n)) (+ n (sum-counts xs)))))

(defthm countsp-of-bump
  (implies (countsp xs) (countsp (bump xs k n))))

(defthm len-of-bump
  (equal (len (bump xs k n)) (len xs)))

(defthm bump-bump-same
  (implies (and (countsp xs) (natp k) (< k (len xs)) (natp n) (natp m))
           (equal (bump (bump xs k n) k m) (bump xs k (+ n m))))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable bump))

(defthm fused-step-square
  (implies (fused-rel a b)
           (fused-rel (fused-step a l) (ref-run b (fused-h l)))))

(defthm fused-edge
  (implies (fused-rel a b) (equal (fused-obs a q) (ref-obs b q))))

; The whole-run claim, by functional instance: no induction here.
(defthm fused-refines-reference
  (implies (fused-rel a b)
           (equal (fused-obs (fused-run a w) q)
                  (ref-obs (ref-run b (fused-expand w)) q)))
  :hints (("Goal" :use ((:functional-instance sq-paste-obs
                         (sq-a-init fused-init) (sq-b-init ref-init)
                         (sq-a-step fused-step) (sq-b-step ref-step)
                         (sq-h fused-h)
                         (sq-a-obs fused-obs) (sq-b-obs ref-obs)
                         (sq-rel fused-rel)
                         (sq-a-run fused-run) (sq-b-run ref-run)
                         (sq-expand fused-expand))))))

(defthm fused-base (fused-rel (fused-init) (ref-init)))

; ----------------------------------------------------------------------
; Teeth: a fused step that forgets the second chunk in its cached total.

(defun fused-step-bad (a l)
  (if (recv2-p l)
      (let ((k (cadr l)) (n (caddr l)) (m (cadddr l)))
        (cons (bump (car a) k (+ n m)) (+ (nfix (cdr a)) n)))
    a))

; Evaluated: one fused receive and the totals disagree.
(assert-event
 (let ((l '(:recv2 1 5 7)))
   (and (equal (fused-obs (fused-step (fused-init) l) '(:total)) 12)
        (equal (fused-obs (fused-step-bad (fused-init) l) '(:total)) 5)
        (equal (ref-obs (ref-run (ref-init) (fused-h l)) '(:total)) 12))))

; Proved: the mutant's step obligation is false at a related pair, so no
; functional instance of SQ-STEP exists for it.
(defthm fused-step-bad-breaks-square
  (let ((a (fused-init)) (b (ref-init)) (l '(:recv2 1 5 7)))
    (and (fused-rel a b)
         (not (fused-rel (fused-step-bad a l) (ref-run b (fused-h l)))))))
