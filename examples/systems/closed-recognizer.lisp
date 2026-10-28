; examples/systems/closed-recognizer.lisp
;
; "Never open a recognizer to prove a property of a transition" (fn
; docs/proof-style.md, the section of that name; fn's
; fn-deftransition-closed / fn-deftransition write the mechanical parts).
; The content is proved once per owning transition, with the recognizer
; open in that proof only; the dispatcher's keystone is proved with the
; recognizer and its sub-recognizers CLOSED, by :use of the per-transition
; lemmas, and its theory is pinned at the form.
;
; Cited by humans/04-modelling-systems.md, "State machines and step
; functions".

(in-package "ACL2")

(defun phasep (x) (member-eq x '(:open :closed)))

(defun line-listp (x)
  (if (atom x) (null x) (and (stringp (car x)) (line-listp (cdr x)))))

(defun sess (phase lines limit) (list phase lines limit))
(defun sess-phase (s) (nth 0 s))
(defun sess-lines (s) (nth 1 s))
(defun sess-limit (s) (nth 2 s))

(defun sessionp (s)
  (and (true-listp s) (equal (len s) 3)
       (phasep (sess-phase s))
       (line-listp (sess-lines s))
       (natp (sess-limit s))
       (<= (len (sess-lines s)) (sess-limit s))))

; Transitions.
(defun sess-recv (line s)
  (if (and (eq (sess-phase s) :open) (stringp line)
           (< (len (sess-lines s)) (sess-limit s)))
      (sess :open (cons line (sess-lines s)) (sess-limit s))
    s))

(defun sess-close (s)
  (sess :closed (sess-lines s) (sess-limit s)))

(defun sess-drain (s)
  (sess (sess-phase s) nil (sess-limit s)))

(defun sess-step (e s)
  (cond ((and (consp e) (eq (car e) :line)) (sess-recv (cadr e) s))
        ((eq e :close) (sess-close s))
        ((eq e :drain) (sess-drain s))
        (t s)))

; ---------------------------------------------------------------------------
; The content, at each owning transition, with the recognizer open here.

(defthm sess-recv-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-recv line s))))

(defthm sess-close-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-close s))))

(defthm sess-drain-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-drain s))))

; The closed theory: the recognizer, its sub-recognizers and the
; transitions, withdrawn by one name.
(deftheory sess-closed
  '(sessionp phasep line-listp sess-recv sess-close sess-drain))
(in-theory (disable sess-closed))

; KEYSTONE: the dispatcher preserves the recognizer.  Proved with everything
; closed, by the per-transition lemmas.  The theory is pinned at the form, so
; no later in-theory widens it.
(defthm sess-step-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-step e s)))
  :hints (("Goal" :in-theory (union-theories
                              '(sess-step sess-recv-preserves-sessionp
                                sess-close-preserves-sessionp
                                sess-drain-preserves-sessionp)
                              (theory 'minimal-theory)))))

; A branch lemma for a transition that cannot touch the property: an
; unknown event is a no-op.  :rule-classes nil, cited by :use.
(defthm sess-step-unknown-is-no-op
  (implies (and (not (consp e)) (not (eq e :close)) (not (eq e :drain)))
           (equal (sess-step e s) s))
  :rule-classes nil)

; Teeth: a reachable witness, and the removal witness for (SESSIONP S).
(assert-event
 (let ((s (sess :open nil 2)))
   (and (sessionp s) (sessionp (sess-step '(:line "x") s)))))

(assert-event
 (let ((bad (sess :open '("a" "b" "c") 2)))
   (and (not (sessionp bad)) (not (sessionp (sess-step :close bad))))))
