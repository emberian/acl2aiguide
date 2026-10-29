; examples/assured/registry-emit.lisp
;
; What it shows: the measured limit of exporting a declaration registry
; by reading world tables, and the remedy, at the size of one page
; (fn2's experiment: LEAN-METATHEORY.md section 5.3, "Control 2: a
; behaviour-only mutation does not"; the mutation script is
; fn2/meta/emit/mutations/retired-behaviour.sh @dddc32d34).
;
; A declaration macro DEFKIND records a row in the table ASSURED-KINDS and
; generates a behaviour function NAME-OBSERVES-P, which must refuse every
; event in the :retired phase.  fn2's mutation changed the GENERATOR (the
; macro body), not the declaration: the row is written exactly as before.
; One world cannot hold two versions of one macro, so the book defines the
; mutated generator beside the real one, DEFKIND-MUTANT, and declares the
; same kind once with each.
;
;   - The table-only export (EXPORT-ROW) prints the two rows identically:
;     a reader of the table cannot see the change.
;   - The behaviour differs: the mutant observes an event while retired.
;   - The manifest export (EXPORT-ROW-WITH-BODIES) adds, for each generated
;     function the row names, its admitted body as the world stores it.
;     The two manifests differ.  A fingerprint of that text (here the body
;     itself) is evidence that something changed; it says nothing about
;     whether the new body is right.
;
; Cited by assured/humans/06-metatheory-split.md and
; assured/ai/06-metatheory-split.md.

(in-package "ACL2")

(defun rk-sym (a b)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name a) (symbol-name b)) 'acl2))

(defmacro defkind (name &key states observes)
  (let ((obs (rk-sym name '-observes-p)))
    `(progn
       (defun ,obs (phase event)
         (declare (xargs :guard t))
         (and (not (equal phase ,(position-eq :retired states)))
              (if (member-eq event ',observes) t nil)))
       (table assured-kinds ',name
              '(:states ,states :observes ,observes :generated (,obs))))))

; The generator after a behaviour-only mutation: same row, the retired
; exclusion gone from the generated body.
(defmacro defkind-mutant (name &key states observes)
  (let ((obs (rk-sym name '-observes-p)))
    `(progn
       (defun ,obs (phase event)
         (declare (xargs :guard t) (ignore phase))
         (if (member-eq event ',observes) t nil))
       (table assured-kinds ',name
              '(:states ,states :observes ,observes :generated (,obs))))))

(defkind echo-v1
  :states (:free :reply :retired)
  :observes (:receive-result :send-result))

(defkind-mutant echo-v2
  :states (:free :reply :retired)
  :observes (:receive-result :send-result))

; The table-only export: the row, without the kind's own name.  The
; generated names differ only by the kind's name, so they are printed
; relative to it.
(defun rk-strip (generated name)
  (declare (xargs :verify-guards nil))
  (if (atom generated) nil
    (cons (subseq (symbol-name (car generated)) (length (symbol-name name))
                  (length (symbol-name (car generated))))
          (rk-strip (cdr generated) name))))

(defun export-row (name wrld)
  (declare (xargs :verify-guards nil))
  (let ((row (cdr (assoc-eq name (table-alist 'assured-kinds wrld)))))
    (list :states (cadr (member-eq :states row))
          :observes (cadr (member-eq :observes row))
          :generated (rk-strip (cadr (member-eq :generated row)) name))))

(defun rk-bodies (generated wrld)
  (declare (xargs :verify-guards nil))
  (if (atom generated) nil
    (cons (getpropc (car generated) 'unnormalized-body nil wrld)
          (rk-bodies (cdr generated) wrld))))

(defun export-row-with-bodies (name wrld)
  (declare (xargs :verify-guards nil))
  (let ((row (cdr (assoc-eq name (table-alist 'assured-kinds wrld)))))
    (append (export-row name wrld)
            (list :bodies (rk-bodies (cadr (member-eq :generated row)) wrld)))))

; 1. The table-only exports are identical.
(assert-event (equal (export-row 'echo-v1 (w state))
                     (export-row 'echo-v2 (w state))))

; 2. The behaviour is not: a retired echo row must not observe a result.
(assert-event (equal (echo-v1-observes-p 2 :send-result) nil))
(assert-event (equal (echo-v2-observes-p 2 :send-result) t))

; 3. The manifest export binds each generated name to its admitted body,
;    and the two manifests differ.
(assert-event (not (equal (export-row-with-bodies 'echo-v1 (w state))
                          (export-row-with-bodies 'echo-v2 (w state)))))
