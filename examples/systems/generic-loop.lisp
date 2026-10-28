; examples/systems/generic-loop.lisp
;
; The loop-twin bridge proved ONCE, over constrained functions, and obtained
; for each instance by :functional-instance with no induction and no
; instance-specific lemma: the mechanism of fn's def-loop (fn
; books/def-loop.lisp header: "each SHAPE's bridge is proved ONCE, over
; constrained functions that have no axioms ... every instance obtains its
; bridge by :functional-instance of that one theorem ... no instance
; induction, no instance hint").  Compare examples/modelling/mbe-loop-twin.lisp,
; where the bridge is proved by induction for one function.
;
; Cited by humans/04-modelling-systems.md, "Functional instantiation and
; generic layers".

(in-package "ACL2")

; The shape: a filter-map.  KEEP and F have no constraints at all; the local
; witnesses only show the signatures can be met.
(encapsulate
  (((gl-keep *) => *) ((gl-f *) => *))
  (local (defun gl-keep (x) (declare (ignore x)) t))
  (local (defun gl-f (x) x)))

(defun gl-map (xs)
  (if (consp xs)
      (if (gl-keep (car xs))
          (cons (gl-f (car xs)) (gl-map (cdr xs)))
        (gl-map (cdr xs)))
    nil))

(defun gl-map-loop (xs acc)
  (if (consp xs)
      (gl-map-loop (cdr xs)
                   (if (gl-keep (car xs)) (cons (gl-f (car xs)) acc) acc))
    (revappend acc nil)))

; The one induction.
(defthm gl-map-loop-is-revappend
  (equal (gl-map-loop xs acc) (revappend acc (gl-map xs))))

; ---------------------------------------------------------------------------
; An instance: squares of the odd elements, as an mbe pair.

(defun sq-odds-loop (xs acc)
  (declare (xargs :guard (and (integer-listp xs) (true-listp acc))))
  (if (consp xs)
      (sq-odds-loop (cdr xs)
                    (if (oddp (car xs)) (cons (* (car xs) (car xs)) acc) acc))
    (revappend acc nil)))

(defun sq-odds (xs)
  (declare (xargs :guard (integer-listp xs) :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (if (oddp (car xs))
                      (cons (* (car xs) (car xs)) (sq-odds (cdr xs)))
                    (sq-odds (cdr xs)))
                nil)
       :exec (sq-odds-loop xs nil)))

; The instance's bridge.  The obligations ACL2 generates are the defining
; equations of GL-MAP and GL-MAP-LOOP under the substitution, i.e. the
; definitions of SQ-ODDS and SQ-ODDS-LOOP; one unfold of each closes them,
; in a theory of nothing but those two definitions.  No induction.
(defthm sq-odds-loop-is-revappend
  (equal (sq-odds-loop xs acc) (revappend acc (sq-odds xs)))
  :hints (("Goal"
           :use ((:functional-instance gl-map-loop-is-revappend
                                       (gl-keep (lambda (x) (oddp x)))
                                       (gl-f (lambda (x) (* x x)))
                                       (gl-map sq-odds)
                                       (gl-map-loop sq-odds-loop)))
           :in-theory (union-theories '(sq-odds sq-odds-loop)
                                      (theory 'minimal-theory)))))

(verify-guards sq-odds
  :hints (("Goal" :use ((:instance sq-odds-loop-is-revappend (acc nil)))
           :in-theory (union-theories '(sq-odds revappend)
                                      (theory 'minimal-theory)))))

(assert-event (equal (sq-odds '(1 2 3 4 5)) '(1 9 25)))
