; examples/modelling/defaggregate-define.lisp
;
; The library alternative to a hand-written record: std::defaggregate
; generates the recognizer, constructor, accessors and their basic theorems
; (with the definitions left disabled); std::define with :returns states and
; proves the type of a function's result beside its definition.  Compare
; examples/modelling/opaque-record.lisp, which writes the same discipline
; by hand over a positional list.
;
; Cited by humans/03-modelling-data.md, "Records".

(in-package "ACL2")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/define" :dir :system)

(std::defaggregate post
  ((id stringp)
   (body stringp)
   (groups string-listp))
  :tag :post)

; The layout is NOT positional: by default the constructor builds
; (:POST (ID . id) (BODY . body) (GROUPS . groups)) and each accessor is an
; ASSOC (see :pcb! of the event).  A host that encodes records as positional
; lists does not read this layout.
(assert-event
 (equal (post "<1@x>" "hi" '("g"))
        '(:post (id . "<1@x>") (body . "hi") (groups "g"))))

; The generated rules, by the names the event gives them.
(defthm post-generated-rules-hold
  (and (equal (post->id (post id body groups)) id)
       (implies (post-p x) (stringp (post->id x)))
       (implies (and (stringp id) (stringp body) (string-listp groups))
                (post-p (post id body groups))))
  :hints (("Goal" :in-theory (union-theories
                              '(post->id-of-post return-type-of-post->id
                                post-p-of-post)
                              (theory 'minimal-theory))))
  :rule-classes nil)

; std::define: guards in the formals; the result's type proved as a named
; rewrite rule (POST-P-OF-CROSSPOST), under the guard as hypothesis.
(define crosspost ((g stringp) (p post-p))
  :returns (new post-p :hyp :guard
                :name post-p-of-crosspost)
  (change-post p :groups (cons g (post->groups p))))

(defthm post->id-of-crosspost
  (equal (post->id (crosspost g p)) (post->id p))
  :hints (("Goal" :in-theory (enable crosspost))))

; After the event the definition is disabled (:DOC define, :enabled: by
; default the function is disabled after the define is processed), so
; the proof above enabled it in its own hint.
(assert-event
 (not (member-equal '(:definition crosspost) (current-theory-fn :here (w state)))))
