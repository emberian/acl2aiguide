; examples/modelling/opaque-record.lisp
;
; A raw-list record under an opaque discipline, written out by hand in the
; shape fn's fn-defrecord generates (fn docs/proof-style.md section 1): a
; shape predicate, total accessors whose :logic is the raw selector and
; whose :exec is a total helper, a constructor, the shape lemma and one
; accessor-of-constructor lemma per field immediately after it, the
; forward-chaining shape facts that opacity would otherwise take away, the
; :definition runes withdrawn under a NAME-internals theory, and a
; recognizer written over the shape and the accessors.
;
; Cited by humans/03-modelling-data.md, "Records".

(in-package "ACL2")

; Total helpers: the :exec side of every accessor, guard T.
(defun ag-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun ag-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

; ---------------------------------------------------------------------------
; The record (:art id body groups): a tag at index 0, three fields.

(defun art-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (equal (car x) :art)))

(defun art-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (ag-car (ag-cdr x))))
(verify-guards art-id)

(defun art-body (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x))) :exec (ag-car (ag-cdr (ag-cdr x)))))
(verify-guards art-body)

(defun art-groups (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (ag-car (ag-cdr (ag-cdr (ag-cdr x))))))
(verify-guards art-groups)

(defun make-art (id body groups)
  (declare (xargs :guard t))
  (list :art id body groups))

; The record lemmas, right after the constructor, in accessor vocabulary.
(defthm art-shapep-of-make-art
  (art-shapep (make-art id body groups)))
(defthm art-id-of-make-art
  (equal (art-id (make-art id body groups)) id))
(defthm art-body-of-make-art
  (equal (art-body (make-art id body groups)) body))
(defthm art-groups-of-make-art
  (equal (art-groups (make-art id body groups)) groups))

; What opacity takes away and must be exported back, as forward-chaining
; rules only: the consp/true-listp facts type reasoning used to get by
; opening the accessors.
(defthm art-shapep-forward-shape
  (implies (art-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defthm art-accessors-forward-consp
  (and (implies (art-id x) (consp x))
       (implies (art-body x) (consp x))
       (implies (art-groups x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (art-id x) (consp x))
                                    :trigger-terms ((art-id x)))
                 (:forward-chaining :corollary (implies (art-body x) (consp x))
                                    :trigger-terms ((art-body x)))
                 (:forward-chaining :corollary (implies (art-groups x) (consp x))
                                    :trigger-terms ((art-groups x)))))

; Injectivity as a named fact for :use, never a global rewrite rule.
(defthm make-art-injective
  (implies (equal (make-art id1 body1 groups1) (make-art id2 body2 groups2))
           (and (equal id1 id2) (equal body1 body2) (equal groups1 groups2)))
  :rule-classes nil)

; Withdraw only the :definition runes; type prescriptions and executable
; counterparts stay, so ground terms still evaluate.
(deftheory art-internals
  '((:d art-shapep) (:d art-id) (:d art-body) (:d art-groups) (:d make-art)))
(in-theory (disable art-internals))

; ---------------------------------------------------------------------------
; The recognizer, over the shape and the accessors, never over car/len.

(defun string-listp* (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (stringp (car x)) (string-listp* (cdr x)))))

(defun artp (x)
  (declare (xargs :guard t))
  (and (art-shapep x)
       (stringp (art-id x))
       (stringp (art-body x))
       (string-listp* (art-groups x))
       (consp (art-groups x))))

(defthm artp-forward-shape
  (implies (artp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defthm artp-of-make-art
  (equal (artp (make-art id body groups))
         (and (stringp id) (stringp body)
              (string-listp* groups) (consp groups))))

; A transition stated and proved in accessor vocabulary.  Nothing here opens
; the record; the proof uses only the record lemmas.
(defun art-crosspost (g m)
  (declare (xargs :guard (and (stringp g) (artp m))))
  (make-art (art-id m) (art-body m) (cons g (art-groups m))))

(defthm artp-of-art-crosspost
  (implies (and (stringp g) (artp m))
           (artp (art-crosspost g m))))

(defthm art-id-of-art-crosspost
  (equal (art-id (art-crosspost g m)) (art-id m)))

; The one form that must open the record opens it in its own hint, by the
; internals name, never book-wide.
(defthm art-shapep-is-len-4
  (implies (art-shapep x) (equal (len x) 4))
  :hints (("Goal" :in-theory (enable art-internals)))
  :rule-classes nil)

; Export theory at the book's end: the recognizer and the transition are
; withdrawn; the record lemmas and keystones stay enabled.
(in-theory (disable artp art-crosspost))

; Teeth for the keystone artp-of-art-crosspost: a reachable witness and one
; violating value per hypothesis, each an assert-event on concrete values.
; A violating value lies outside the guard by construction, so it is
; evaluated for its LOGICAL value under (with-guard-checking :none ...);
; without that the assert-event itself stops on the guard violation
; (fn docs/proof-style.md section 5).
(defconst *m0* (make-art "<1@x>" "hello" '("comp.lang")))
(assert-event (and (artp *m0*) (artp (art-crosspost "alt.test" *m0*))))
(assert-event
 (with-guard-checking :none
   (and (artp *m0*) (not (artp (art-crosspost 7 *m0*))))))
(assert-event
 (with-guard-checking :none
   (and (stringp "alt.test")
        (not (artp (art-crosspost "alt.test" (make-art 1 "b" '("g"))))))))
