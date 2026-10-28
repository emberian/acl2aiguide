; examples/shapes/includes-user.lisp
;
; What an includer of includes.lisp gets: its non-local events, as the
; export event left them.  The locally included book's rules are absent, so a
; proof that needed them there fails here (the "local lemma used by a
; dependent" pitfall), and the export-disabled rule must be enabled where it
; is used.
;
; Cited by ai/01-form-shapes.md, "include-book".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "includes")

; From the non-local include: present.
(assert-event (getpropc 'rev-of-append 'theorem nil (w state)))
; From the local include: absent.
(assert-event (not (getpropc 'len-of-take 'theorem nil (w state))))
; From the book itself, disabled by its export event.
(assert-event (equal (disabledp 'len-of-take-of-rev) '((:rewrite len-of-take-of-rev))))

; LEN-OF-TAKE closes this goal by rewriting alone in includes.lisp; here,
; without it, rewriting alone does not.
(local
 (must-fail
  (thm (implies (natp n) (equal (len (take n x)) n))
       :hints (("Goal" :do-not-induct t)))))

; Enable the exported rule in the one hint that needs it.
(defthm len-of-take-of-rev-again
  (implies (natp n) (equal (len (take n (rev y))) n))
  :hints (("Goal" :in-theory (enable len-of-take-of-rev))))
