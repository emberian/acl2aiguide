; examples/fn-lessons/loop-bridge-once.lisp
;
; What it shows: fn's def-loop idea in miniature.  The equivalence between a
; structural recursion (the :logic body) and its accumulator loop (the :exec
; body) is proved ONCE, by induction, over a constrained element function
; that has no axioms.  Each concrete loop then obtains its bridge by
; :functional-instance; the obligations are the definitional equations of
; the two concrete functions, discharged by unfolding in minimal-theory, with
; no induction per instance (:doc encapsulate, :doc lemma-instance,
; :doc mbe).
;
; Cited by fn-lessons/22-def-loop.md, "The shape to copy".

(in-package "ACL2")

; --- the library: one constrained function, one shape, one bridge

(encapsulate
  (((lb-f *) => *))
  (local (defun lb-f (x) x)))

(defun lb-map (xs)
  (if (consp xs)
      (cons (lb-f (car xs)) (lb-map (cdr xs)))
    nil))

(defun lb-map-loop (xs acc)
  (if (consp xs)
      (lb-map-loop (cdr xs) (cons (lb-f (car xs)) acc))
    (revappend acc nil)))

(defthm lb-map-loop-is-revappend
  (equal (lb-map-loop xs acc) (revappend acc (lb-map xs)))
  :hints (("Goal" :induct (lb-map-loop xs acc))))

; --- an instance: the loop, the wrapper with the mbe, the bridge by
; functional instance, the two guard proofs

(defun double-all-loop (xs acc)
  (declare (xargs :guard (and (rational-listp xs) (true-listp acc))
                  :verify-guards nil))
  (if (consp xs)
      (double-all-loop (cdr xs) (cons (* 2 (car xs)) acc))
    (revappend acc nil)))

(defun double-all (xs)
  (declare (xargs :guard (rational-listp xs) :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (cons (* 2 (car xs)) (double-all (cdr xs)))
                nil)
       :exec (double-all-loop xs nil)))

(local
 (defthm double-all-loop-is-revappend
   (equal (double-all-loop xs acc) (revappend acc (double-all xs)))
   :hints (("Goal"
            :use ((:functional-instance lb-map-loop-is-revappend
                                        (lb-f (lambda (x) (* 2 x)))
                                        (lb-map double-all)
                                        (lb-map-loop double-all-loop)))
            :in-theory (union-theories '(double-all double-all-loop)
                                       (theory 'minimal-theory))))))

(verify-guards double-all-loop)
(verify-guards double-all)
(in-theory (disable double-all-loop))

(assert-event (equal (double-all '(1 2 3)) '(2 4 6)))
