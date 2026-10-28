# 04. `defabsstobj` obligations written out by hand

## The wound

An abstract stobj is admitted only after its correspondence, preservation and
guard obligations are proved, and fn wrote those obligations out by hand.
The proof-engineering inventory of 2026-10-01: "21 `defabsstobj` in 18 books
(78 `defstobj`, 67 array fields, 9 hash-table fields, 310 `stobj-let`, 30
`with-local-stobj`, 34 `:congruent-to`). The obligations `{correspondence}`,
`{preserved}`, `{guard-thm}` are stated "exactly as
`defabsstobj-missing-events` prints it and proved before the `defabsstobj`
event, which then admits them by name" ...: 285 such theorems in 13 books";
the catalog's block alone was 2,595 lines for 22 exports, and the blocks
total "About 5,770 lines ...; the 18 books total 21,760 lines and 90 s of
certification CPU" [fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:136-156 @worktree].
The catalog block is pinnable in history: the obligations comment at line
2038 and the `defabsstobj fn-cat` event at line 4633, 2,595 lines apart
[fn: books/catalog.lisp:2038,4633 @4e56f2d01]. One of them:

```lisp
(defthm fn-cat-at{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-at seq fn-cat$c) (fn-cat$a-at seq fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))
```
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:160-166 @worktree].

Two ACL2 rules shaped the rest. Congruent stobjs must match exactly, so
"adding an export here adds it to every abstract stobj declared
`:congruent-to fn-octets`" and the octet buffer had seven hand clones
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:169-174 @worktree].
And the attachment restriction: the catalog's recognizer reached `fn-digest`,
which another book attaches, so the recognizer and correspondence had to be
restated over a digest-free row shape, and "every book that needs the held
recognizer carries `fn-held-listp` beside `fn-cat-p`"
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:175-181 @worktree].
The manual's rule is "No supporter of a stobj recognizer is allowed to have an
attachment", and for `defabsstobj` "there must be a correspondence function
whose supporters are not allowed to have attachments"
[:doc stobj-attachment-restrictions].

## What was done about it

The generator `def-representation` (promoted from the `defadt` prototype)
declares an abstract stobj "from one declaration of its schema" and generates
"the obligations obtained from ACL2 itself by `defabsstobj-missing-events` and
closed by one uniform hint, the `defabsstobj`, the `-is-` meaning of each
export"; it adds "the ATTACHMENT CHECK at expansion": the ancestors of what
the recognizer and correspondence will call are checked in the world "BEFORE
anything is generated, with `canonical-ancestors-lst` and `attached-fns`, the
functions ACL2's own check uses, and a reachable attachment is refused by
name" [fn: books/def-representation.lisp:1-29 @3bbfc4dca]. The prototype's
cost was measured: "147 theorems, 9.4 s once; 2 to 3 s per instance", against
"`books/catalog.lisp` at 12.2 s and 2,595 hand lines for one 22-export"
abstract stobj [fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:23,356-357 @worktree].
The paged catalog's row is one declaration:

```lisp
(def-representation fn-crow
  (seq :u64) (txid :u64) (gen :u64) (payload :u64) (charge :u64) (stamp :u64)
  (msgid :octets)
  (wpres :bool) (wat :u64) (wby :u64)
  (esc :bool)
  (aux :tree)
  (nums :tree)
  :write-once t
  :pages t)
```
[fn: books/catalog-paged.lisp:101-109 @3bbfc4dca].

The generator did not replace the hand blocks it was built for. At
`origin/dev`, 271 hand-stated obligation theorems remain in 9 books
(`catalog-logic` 65, `payload-arena-extent` 40, `catalog-paged` 38,
`runtime-contract-pool` 37, `octets-stobj` 34, `history-records` 21,
`incoming-copy-stobj` 14, `history-paged` 13, `catalog-dense-map` 9), against
`def-representation` forms in 5 books
[measured: `git -C ~/dev/fn grep -c -E '^\(defthm [^ ]*\{(correspondence|preserved|guard-thm)' 3bbfc4dca -- books`
and `... grep -c -E '^ *\(def-representation ' 3bbfc4dca -- books`, 2026-10-28, laptop].
The catalog's block moved, whole, into `catalog-logic.lisp` when the catalog
was split [fn: books/catalog-logic.lisp:2372 @3bbfc4dca]. That is lesson 01's
disease at the level of proof: the generator landed beside the hand form.

## The lesson

Never write an abstract stobj's obligations by hand; obtain them from ACL2
and close them by a uniform hint inside a generator, because
`defabsstobj-missing-events` exists for that: "just replace a call of
`defabsstobj` by a call of `defabsstobj-missing-events` on the same
arguments", and the value is "the list of all objects `(name formula
. old-formula)`, where a `defthm` event named `name` remains to be admitted"
[:doc defabsstobj-missing-events]. Check the attachment restriction before
generating anything, as the manual's own check does
[:doc stobj-attachment-restrictions]. Keep the export list of an octet buffer
small and fixed, since a congruent stobj must have "exactly the same
structure" [:doc defstobj]. And when the generator lands, migrate the hand
instances in the same landing, or count them where a gate will fail.

## The shape to copy

One schema declaration per representation, as `fn-crow` above, with the
generator's options listed in its own header
[fn: books/def-representation.lisp:6-10 @3bbfc4dca]:

```lisp
;   (def-representation NAME (FIELD KIND) ...
;     [:scalar t] [:generic t] [:invariant PRED :invariant-lemmas (L ...)]
;     [:write-once t] [:paged nil]
;     [:exports ((ROLE [:as EXPORT] [:logic FN]) ...)] [:source SRC]
;     [:model (:recognizer R :creator C)] [:lemmas (THM ...)])
```

For the ACL2 side of abstract stobjs (foundations, `:corr-fn`, `:protect`,
attachable stobjs) read the manual's topics in order: `defabsstobj`,
`defabsstobj-missing-events`, `attach-stobj`, `stobj-attachment-restrictions`;
the manual's worked examples are the community books
`books/demos/defabsstobj-example-1.lisp` and `defabsstobj-example-2.lisp`
[:doc defabsstobj].
