; examples/assured/machine.lisp
;
; What it shows: a machine declaration whose continuations NAME functions,
; checked against the world when the declaration is admitted, in the shape
; fn2's DEFMACHINE moved to after its review (REVIEW-SINS-20261028.md
; finding A23: continuations had been code fragments pasted into generated
; bodies, referring to the generator's private variable names; fn2's
; remedy, R5a pass 3, made them function symbols, fn2/books/machines-a.lisp
; :17-60 @127f7b877).
;
;   (defmach NAME :states (:s0 :s1 ...) :budget (:steps S)
;                 :continuations ((:s0 FN0) (:s1 FN1) ...))
;
; Admission (a MAKE-EVENT that reads the world) refuses the declaration
; unless every state has exactly one continuation and every continuation is
; an existing guard-verified function of two arguments (STEPS ST) returning
; (MV SPENT ST).  Then it emits:
;   - one constant per state and *NAME-STATE-COUNT*;
;   - NAME-RUN: dispatch on the phase to the named continuation, with the
;     budget passed explicitly, refusing an out-of-range phase by name
;     (:BAD-PHASE), never by falling into a default arm;
;   - a row in the ASSURED-MACHINES table: the declaration, as data.
; The continuation's own guard is the contract the dispatch inherits: the
; dispatch's guard verification succeeds only because each continuation
; is guard-verified for a budget of at most S steps.
;
; Cited by assured/humans/01-rules-as-declarations.md and
; assured/ai/01-rules-as-declarations.md.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun am-sym (a b)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name a) (symbol-name b)) 'acl2))

(defun am-consts (name states n)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons `(defconst ,(am-sym '* (am-sym name (am-sym '-state- (am-sym (car states) '*)))) ,n)
          (am-consts name (cdr states) (+ 1 n)))))

(defun am-arms (states conts n)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons `(,n (,(cadr (assoc-eq (car states) conts)) steps st))
          (am-arms (cdr states) conts (+ 1 n)))))

; A continuation must already exist, take (STEPS ST), be guard-verified.
(defun am-continuations-okp (conts wrld)
  (declare (xargs :verify-guards nil))
  (or (null conts)
      (and (consp (car conts))
           (symbolp (cadar conts))
           (function-symbolp (cadar conts) wrld)
           (equal (formals (cadar conts) wrld) '(steps st))
           (eq (symbol-class (cadar conts) wrld) :common-lisp-compliant)
           (am-continuations-okp (cdr conts) wrld))))

(defmacro defmach (name &key states budget continuations)
  `(make-event
    (let ((wrld (w state)))
      (if (and (symbolp ',name)
               (consp ',states) (symbol-listp ',states)
               (no-duplicatesp-eq ',states)
               (equal (strip-cars ',continuations) ',states)
               (posp (cadr (member-eq :steps ',budget)))
               (am-continuations-okp ',continuations wrld))
          (value
           '(progn
              ,@(am-consts name states 0)
              (defconst ,(am-sym '* (am-sym name '-state-count*)) ,(len states))
              (defun ,(am-sym name '-run) (phase steps st)
                (declare (xargs :guard (and (natp steps)
                                            (<= steps ,(cadr (member-eq :steps budget)))
                                            (st-p st))))
                (case phase
                  ,@(am-arms states continuations 0)
                  (otherwise (mv :bad-phase st))))
              (table assured-machines ',name
                     '(:states ,states :budget ,budget
                       :continuations ,continuations))))
        (er soft 'defmach
            "~x0: every state needs one continuation, and every ~
             continuation must be an existing guard-verified function of ~
             (STEPS ST)."
            ',name)))))

; ----------------------------------------------------------------------
; An instance: a two-state copier whose state ST is (pending . copied).

(defun st-p (st)
  (declare (xargs :guard t))
  (and (consp st) (natp (car st)) (natp (cdr st))))

; Each continuation spends at most STEPS and answers (mv spent st).
(defun copier-idle (steps st)
  (declare (xargs :guard (and (natp steps) (st-p st))) (ignore steps))
  (mv 0 st))

(defun copier-copy (steps st)
  (declare (xargs :guard (and (natp steps) (st-p st))))
  (let ((n (min steps (car st))))
    (mv n (cons (- (car st) n) (+ (cdr st) n)))))

(defmach copier
  :states (:idle :copy)
  :budget (:steps 32)
  :continuations ((:idle copier-idle) (:copy copier-copy)))

(assert-event (equal *copier-state-copy* 1))
(assert-event (equal *copier-state-count* 2))
(assert-event
 (equal (cdr (assoc-eq 'copier (table-alist 'assured-machines (w state))))
        '(:states (:idle :copy) :budget (:steps 32)
          :continuations ((:idle copier-idle) (:copy copier-copy)))))

(assert-event (equal (mv-list 2 (copier-run *copier-state-copy* 32 '(40 . 0)))
                     '(32 (8 . 32))))
(assert-event (equal (mv-list 2 (copier-run 7 32 '(40 . 0)))
                     '(:bad-phase (40 . 0))))

; Refused at admission: a continuation that is a form, not a function.
(must-fail
 (defmach pasted
   :states (:idle)
   :budget (:steps 32)
   :continuations ((:idle (mv 0 st)))))

; Refused at admission: a continuation that does not exist yet.
(must-fail
 (defmach early
   :states (:idle :copy)
   :budget (:steps 32)
   :continuations ((:idle copier-idle) (:copy copier-copy-later))))

; Refused at admission: a state without a continuation.
(must-fail
 (defmach partial
   :states (:idle :copy :drain)
   :budget (:steps 32)
   :continuations ((:idle copier-idle) (:copy copier-copy))))
