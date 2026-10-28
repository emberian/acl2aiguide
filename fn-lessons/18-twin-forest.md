# 18. The twin forest: 361 books copied to make events `local`

## The wound

Landing B (one-world vocabulary) set out to export from each generic only
the runes its includers need. It "measured a per-rune export set S and hit
three edges in sequence, each a ground refusal, each ACL2's own locality rule
rather than a proof gap": a mixed-rule-class event "exports all its runes or
none"; "an exported event's formula, body or guard may name only exported
definitions"; and "a constrained function's non-local constraint theorems
(constraint-info) are part of its definition and cannot be LOCAL without a
redefinition" [fn: build/coordinator/RULINGS.md:50-55 @worktree]. A fourth
kind arrived next ("a `:congruence` or `:refinement` needs its
`:equivalence`") [fn: build/coordinator/RULINGS.md:57-58 @worktree].

Then the worker "reached its certify boundary by COPYING 361 shared-closure
books (190,880 lines) into books/one-world-b-private/, because making events
LOCAL inside a shared library breaks the library's other includers"
[fn: build/coordinator/RULINGS.md:61 @worktree]. The integrator refused it
("twin forest; derived-path law; G4; it already collides"). The root cause:
"most of each implementation's exported universe is shared-library vocabulary
(cbor, defrecord, def-loop, records-shape...), not generic-private"
[fn: build/coordinator/RULINGS.md:61 @worktree].

## What was done about it

The forest was deleted; landing B's sound core landed; the seal itself was
filed as "ONE-WORLD-VOCABULARY, a multi-landing refactor of shared libraries
into public/internal books in place, with the 1% line and the four-edge rule
as its measurement protocol. Not a landing now"
[fn: build/coordinator/RULINGS.md:61 @worktree]. The rule that replaced the
edge-by-edge list: "An edge joins the export set exactly when ACL2's admission
of an UNCHANGED retained event in certify pass 2, with the edge's target
LOCAL, requires it"; "the set is defined by what ACL2 enforces, not by
coordinator judgment" [fn: build/coordinator/RULINGS.md:58 @worktree].

## The lesson

What a book exports is decided inside that book, and once a library has
includers, its interface is changed in the library, in place, never by
copying it. ACL2 fixes what can be hidden: "you can't make an event local if
its presence is required to make sense of a non-local one" [:doc local]; a
local incompatibility "is generally due to the use of a locally defined name
in a non-local event or the failure to make a witnessing definition `local`"
[:doc local-incompatibility]. So a shared library is split at its seam into a
public book (the definitions its theorems mention, and the theorems) and
internal books of proof vocabulary that the public book includes locally
(chapter `humans/02-rewriting-theories-books.md` sections 2.9.1 and 2.9.5).
Design that split when the library is written; retrofitting it across 361
includers is the forest.

## The shape to copy

A library whose proof vocabulary is local and whose interface is the
definitions, the exported theorems and a closing theory event
[example: examples/books/lib.lisp]:

```lisp
(local (include-book "std/lists/take" :dir :system))   ; proof vocabulary

(defun sum-list (x)
  (if (consp x)
      (+ (fix (car x)) (sum-list (cdr x)))
    0))

(local
 (defthm sum-list-of-append-local
   (equal (sum-list (append x y))
          (+ (sum-list x) (sum-list y)))))

(defthm sum-list-of-append-of-cons                      ; the interface
  (equal (sum-list (append x (cons a y)))
         (+ (sum-list x) (fix a) (sum-list y))))

(deftheory lib-internals
  '((:d sum-list) (:i sum-list)))
(in-theory (disable lib-internals))
```

The internal half of a real library is the same `local` include pointed at
the library's own `-internal` book instead of `std/lists/take`.
