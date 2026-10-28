; examples/fn-lessons/tagged-levels.lisp
;
; What it shows: a session wrapped in another session, read one level too
; short.  When the callee's guard says only "a cons", the short reach is
; admitted and answers a plausible wrong value.  When each level has its own
; tagged recognizer and the callee's guard names its level, the short reach
; fails guard verification at definition time (:doc guard, :doc
; verify-guards).  The walk is named once, as a macro that expands to the
; term the call sites spelled, as fn's docs/proof-style.md section 10 does.
;
; Cited by fn-lessons/17-wrong-depth-walks.md, "The shape to copy".

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun post-sessionp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :post) (natp (cdr x))))

(defun auth-sessionp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :auth) (post-sessionp (cdr x))))

; The walk from the outer wrapper to the inner session, named once.
(defmacro auth-post-session (a) `(cdr ,a))

; --- weak: the callee accepts any cons

(defun post-count-weak (s)
  (declare (xargs :guard (consp s)))
  (cdr s))

(defun auth-post-count-weak-short (a)
  (declare (xargs :guard (auth-sessionp a)))
  (post-count-weak a))                    ; one level short: admitted

(assert-event
 (equal (auth-post-count-weak-short '(:auth :post . 3)) '(:post . 3)))
                                          ; a plausible value, not 3

; --- strong: the callee's guard names its level

(defun post-count (s)
  (declare (xargs :guard (post-sessionp s)))
  (cdr s))

(defun auth-post-count (a)
  (declare (xargs :guard (auth-sessionp a)))
  (post-count (auth-post-session a)))

(assert-event (equal (auth-post-count '(:auth :post . 3)) 3))

(local
 (must-fail
  (defun auth-post-count-short (a)
    (declare (xargs :guard (auth-sessionp a)))
    (post-count a))))                     ; the guard proof fails
