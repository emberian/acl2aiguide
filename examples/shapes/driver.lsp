; examples/shapes/driver.lsp -- a REPL driver: one ACL2 session, many forms,
; read the output once.  Run from examples/shapes:
;
;   timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < driver.lsp > driver.out 2>&1
;
; Not a book (cert.pl ignores .lsp); it includes a certified book and works
; above it.  Cited by ai/01-form-shapes.md and ai/02-reading-the-manual.md.

(set-gag-mode :goals)                        ; key checkpoints and goal names only
(set-inhibit-output-lst '(proof-tree))       ; drop proof-tree output
(include-book "hints")                       ; certified closure: seconds, no proofs

; A batch of attempts in one ld: each form printed before it runs, and an
; error does not stop the batch.  Of these three, the second is refused
; ("A :REWRITE rule ... is illegal because it rewrites the variable symbol
; X") and the third fails at a key checkpoint; both reports come out of the
; one run.
(ld '((defthm mag-of-mag
        (implies (rationalp x) (equal (mag (mag x)) (mag x)))
        :hints (("Goal" :cases ((< x 0)))))
      (defthm mag-is-zero-only-at-zero
        (implies (equal (mag x) 0) (equal x 0)))
      (defthm mag-of-neg
        (implies (rationalp x) (equal (mag (- x)) (mag x)))
        :hints (("Goal" :cases ((< x 0))))))
    :ld-pre-eval-print t
    :ld-error-action :continue)

; Every event under a bound, so a search that stops returning costs seconds.
(with-prover-time-limit 10
  (defthm len-of-tk-2 (equal (len (tk 2 x)) 2)))

; Read the world.
:pe mag-non-negative
:pl (mag x)
:pr mag-when-negative

; Break-rewrite: monitor one rule, prove, and answer the break from this
; same input stream.
:brr t
:monitor (:rewrite mag-when-negative) t
(thm (implies (and (rationalp y) (< y 0)) (equal (mag y) (- y))))
:target
:eval
:go
:unmonitor (:rewrite mag-when-negative)
:brr nil
(quit)
