; examples/shapes/absstobj.lisp
;
; Shapes: defabsstobj with every kind of obligation.  The foundation is a
; concrete stobj; the abstract (logical) value is a natural number at most
; 100; three exports cover the three cases -- a reader (CORRESPONDENCE), an
; updater (CORRESPONDENCE, PRESERVED) and an updater whose :EXEC guard asks
; more than the stobj recognizer (CORRESPONDENCE, PRESERVED, GUARD-THM) --
; plus the creator's two.  The events are the ones ACL2 printed when the
; defabsstobj was first submitted without them (kept below as a local
; must-fail), each proved under its printed name.
;
; Cited by ai/01-form-shapes.md, "defabsstobj".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; The foundation.
(defstobj ctr$c
  (val :type (integer 0 *) :initially 0)
  (lim :type (integer 0 *) :initially 100))

; The :LOGIC side: the abstract recognizer, creator and exports.  Each is
; guard-verified (a requirement of defabsstobj).  Names are new: GET would be
; refused ("Symbols in the main Lisp package, such as GET, may not be
; defined or constrained").  An export's guard is its :LOGIC function's guard
; with every :LOGIC function replaced by its export, so it must not use the
; abstract value as an ordinary object: (+ K X) in CTR-ADD$A's guard was
; refused ("A single-threaded object, namely CTR, is being used where an
; ordinary object is expected"); (+ K (CTR-GET$A X)) becomes (CTR-GET CTR).
(defun ctr$ap (x) (declare (xargs :guard t)) (and (natp x) (<= x 100)))
(defun create-ctr$a () (declare (xargs :guard t)) 0)
(defun ctr-get$a (x) (declare (xargs :guard (ctr$ap x))) x)
(defun ctr-incr$a (x)
  (declare (xargs :guard (ctr$ap x)))
  (if (< x 100) (+ 1 x) x))
(defun ctr-add$a (k x)
  (declare (xargs :guard (and (natp k) (ctr$ap x) (<= (+ k (ctr-get$a x)) 100))))
  (+ k x))

; The :EXEC side, over the foundation.
(defun incr$c (ctr$c)
  (declare (xargs :stobjs ctr$c))
  (if (< (val ctr$c) (lim ctr$c))
      (update-val (+ 1 (val ctr$c)) ctr$c)
    ctr$c))

(defun add$c (k ctr$c)
  (declare (xargs :stobjs ctr$c
                  :guard (and (natp k) (<= (+ k (val ctr$c)) (lim ctr$c)))))
  (update-val (+ k (val ctr$c)) ctr$c))

; The correspondence (need not execute: defun-nx).
(defun-nx ctr$corr (ctr$c x)
  (and (ctr$cp ctr$c)
       (equal (lim ctr$c) 100)
       (equal (val ctr$c) x)))

(defmacro ctr-event ()
  '(defabsstobj ctr
     :exports ((ctr-get :logic ctr-get$a :exec val)
               (ctr-incr :logic ctr-incr$a :exec incr$c)
               (ctr-add :logic ctr-add$a :exec add$c))))

; Without the obligations the event fails, after printing them.
(local (must-fail (ctr-event)))

(defthm create-ctr{correspondence}
  (ctr$corr (create-ctr$c) (create-ctr$a))
  :rule-classes nil)

(defthm create-ctr{preserved}
  (ctr$ap (create-ctr$a))
  :rule-classes nil)

(defthm ctr-get{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (equal (val ctr$c) (ctr-get$a ctr)))
  :rule-classes nil)

(defthm ctr-incr{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (ctr$corr (incr$c ctr$c) (ctr-incr$a ctr)))
  :rule-classes nil)

(defthm ctr-incr{preserved}
  (implies (ctr$ap ctr)
           (ctr$ap (ctr-incr$a ctr)))
  :rule-classes nil)

(defthm ctr-add{correspondence}
  (implies (and (ctr$corr ctr$c ctr)
                (natp k)
                (ctr$ap ctr)
                (<= (+ k (ctr-get$a ctr)) 100))
           (ctr$corr (add$c k ctr$c) (ctr-add$a k ctr)))
  :rule-classes nil)

(defthm ctr-add{guard-thm}
  (implies (and (ctr$corr ctr$c ctr)
                (natp k)
                (ctr$ap ctr)
                (<= (+ k (ctr-get$a ctr)) 100))
           (and (natp k)
                (<= (+ k (val ctr$c)) (lim ctr$c))))
  :rule-classes nil)

(defthm ctr-add{preserved}
  (implies (and (natp k)
                (ctr$ap ctr)
                (<= (+ k (ctr-get$a ctr)) 100))
           (ctr$ap (ctr-add$a k ctr)))
  :rule-classes nil)

(ctr-event)

; Callers reason about the abstract value only: (CTR-INCR CTR) is
; (CTR-INCR$A CTR) in the logic, and the foundation never appears.
(defthm ctr-get-of-ctr-incr
  (implies (and (ctrp ctr) (< (ctr-get ctr) 100))
           (equal (ctr-get (ctr-incr ctr)) (+ 1 (ctr-get ctr)))))

(defun ctr-demo ()
  (declare (xargs :guard t))
  (with-local-stobj ctr
    (mv-let (r ctr)
      (let* ((ctr (ctr-incr ctr))
             (ctr (ctr-add 5 ctr)))
        (mv (ctr-get ctr) ctr))
      r)))

(assert-event (equal (ctr-demo) 6))
