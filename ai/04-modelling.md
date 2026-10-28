# ai/04. Modelling: data, stobjs, systems, teeth

Load after `ai/00-pitfalls-first.md`, `ai/01-form-shapes.md` and
`ai/03-prover.md`. The terse twin of `humans/03-modelling-data.md` and
`humans/04-modelling-systems.md`; read those for the why, and `fn-lessons/`
for fn's wounds by name (`04-defabsstobj-by-hand.md`, `08-whole-state-recognizers.md`,
`16-local-stobjs-and-the-repl.md`, `21-crash-model.md`, `22-def-loop.md`,
`23-teeth.md`). Every form is copied from a
certified book under `examples/`. Citations as in `ai/03-prover.md`; fn
coordinator files (`build/coordinator/...`) are untracked and cited
`@worktree 2026-10-28`.

## 0. Pitfalls

| symptom | cause | go to |
| --- | --- | --- |
| checkpoint full of `CAR`, `CDR`, `(NTH *X* ST)` where you expected your names | your vocabulary opened; rules stated in it no longer match | 1, 5 |
| `(consp a)` suddenly unprovable after closing a record | opacity took a type-reasoning fact; export it back as forward chaining | 1 |
| "The name MSGP is in use as a function", "The name PC is in use as a macro" | built-in name clash | 1, 5 |
| a theorem about a guarded function is false at an out-of-guard value | a guard is not a hypothesis | 2 |
| "calls the function F, the guards of which have not yet been verified" | verified code calling unverified code | 2 |
| guard proof fails on a recursive fact it cannot invent | prove the lemma first, `:rule-classes nil`, `:use` it | 2 |
| `mbe` guard goal about accumulator `NIL` fails by induction | bridge lemma must be for every accumulator | 3 |
| "Contrary to the declaration that it is IGNOREd, the variable HIST is used" | `with-local-stobj` body returned the stobj | 6 |
| "the single-threaded object HIST is required" | a stobj argument must be the variable, bind with `let` | 5 |
| "FEES is not the name of a known single-threaded object" | `stobj-let` binds stobj NAMES; use congruent stobjs | 7 |
| "appears capable of modifying the foundational stobj ... non-atomically" | add `:protect t` to that export | 8 |
| one-book attach-stobj: "This is supposed to be impossible!" at re-include | split implementation, attachable, attach into three books | 9 |
| "Illegal attempt to set memoize-table: ... returns a stobj" | stobj-returning functions cannot be memoized | 10 |
| a durability theorem holds for a program missing a fence | the hypotheses ruled the crash out; check teeth | 12, 16 |
| a named assumption no theorem uses | decoration; instantiate it | 13 |
| a green keystone that says nothing | vacuous premise or wrong subject; teeth | 16 |

## Part A: data

## 1. Records: opaque raw lists

Pitfalls: an open accessor turns goals into `car`/`cdr` and your rules stop
matching; closing the record withdraws type-reasoning facts (`(consp a)` from
`(stringp (fn-article-msgid a))`) [fn: docs/proof-style.md:151-160 @3bbfc4dca];
a constructor and shape predicate that disagree show only when the shape lemma
reduces to `NIL` [measured: `(ld "examples/modelling/opaque-record.lisp")` with
the tag mismatched]; injectivity as a global rewrite rule fires on every
constructor equality in every includer [fn: docs/proof-style.md:137-140 @3bbfc4dca].

Rules: total `:guard t` accessors via `mbe`; shape lemma and one
accessor-of-constructor lemma per field right after the constructor; withdraw
only the `:definition` runes under `<record>-internals` (type-prescriptions and
executable counterparts stay); export three shape facts as
`:forward-chaining` only; recognizer written over shape + accessors, never
`len`; injectivity `:rule-classes nil` [fn: docs/proof-style.md:81-88 @3bbfc4dca],
[fn: docs/proof-style.md:116-135 @3bbfc4dca], [fn: docs/proof-style.md:158-182 @3bbfc4dca].
Shape [example: examples/modelling/opaque-record.lisp]:

```lisp
(defun ag-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun ag-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(defun art-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (equal (car x) :art)))

(defun art-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (ag-car (ag-cdr x))))
(verify-guards art-id)

(defun make-art (id body groups)
  (declare (xargs :guard t))
  (list :art id body groups))

(defthm art-shapep-of-make-art
  (art-shapep (make-art id body groups)))
(defthm art-id-of-make-art
  (equal (art-id (make-art id body groups)) id))

(defthm art-shapep-forward-shape
  (implies (art-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defthm make-art-injective
  (implies (equal (make-art id1 body1 groups1) (make-art id2 body2 groups2))
           (and (equal id1 id2) (equal body1 body2) (equal groups1 groups2)))
  :rule-classes nil)

(deftheory art-internals
  '((:d art-shapep) (:d art-id) (:d art-body) (:d art-groups) (:d make-art)))
(in-theory (disable art-internals))
```

(The book has `art-body`, `art-groups`, their lemmas, and the per-accessor
`:forward-chaining` `(implies (art-id x) (consp x))` with `:trigger-terms
((art-id x))`.) The one proof that must open the record names
`art-internals` in its own hint; the book ends `(in-theory (disable artp
art-crosspost))`. The `[Non-rec]` warnings on the record lemmas are expected
[measured: `(ld "examples/modelling/opaque-record.lisp")`].

Alternatives: `std::defaggregate` builds a tagged alist (`(:POST (ID . id) ...)`),
disables its functions and `FORCE`s its type rules; `std::define` with
`:returns` proves return types and disables the function
[example: examples/modelling/defaggregate-define.lisp],
[books: std/util/defaggregate.lisp:47-55], [books: std/util/define.lisp:216-220]:

```lisp
(define crosspost ((g stringp) (p post-p))
  :returns (new post-p :hyp :guard
                :name post-p-of-crosspost)
  (change-post p :groups (cons g (post->groups p))))
```

`fty::defprod` is not certified on the laptop; fn's reason against it is the
include cost and `-fix` normal forms [fn: docs/proof-style.md:719-735 @3bbfc4dca].
An opaque record is a logical interface, not a runtime representation: decide
the two separately [fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:68,178 @worktree 2026-10-28].

## 2. Guards

Pitfalls, each with its form:

- **Not a hypothesis.** "the guard has NO EFFECT on the proof that a recursive
  definition is admissible" and none on the axiom [:doc guard]. `rotl32` guarded
  by `(type (integer 0 31) n)` is false at `n = 40`; the theorem carries the
  range [example: examples/modelling/fixed-width.lisp]:

  ```lisp
  (assert-event
   (with-guard-checking :none
     (not (unsigned-byte-p 32 (rotl32 #xFFFFFFFF 40)))))
  ```

- **Guard proofs fail like any proof**, usually for a recursive fact. The
  checksum's checkpoint was `(< (SUM-BYTES XS) 4294967296)` [measured:
  `checksum32-nohint` after `(ld "examples/modelling/guards.lisp")`]. Prove the
  bound first, `:rule-classes nil`, name it in `:guard-hints`
  [fn: docs/proof-style.md:242-260 @3bbfc4dca]
  [example: examples/modelling/guards.lisp]:

  ```lisp
  (defthm sum-bytes-bound
    (implies (byte-listp* xs)
             (and (natp (sum-bytes xs))
                  (<= (sum-bytes xs) (* 255 (len xs)))))
    :rule-classes nil)

  (defun checksum32 (xs)
    (declare (xargs :guard (and (byte-listp* xs) (< (len xs) 1000000))
                    :guard-hints (("Goal" :use ((:instance sum-bytes-bound))))))
    (the (unsigned-byte 32) (sum-bytes xs)))
  ```

- **Verified may not call unverified**: "The body for REVERSE-AGREES-DIRECT
  calls the function SPEC-REVERSE, the guards of which have not yet been
  verified" [measured: after `(ld "examples/modelling/guards.lisp")`]. Use
  `ec-call` when you mean it (below).
- **A guarded theorem cannot use `implies`**: both arguments are evaluated; use
  the `if` form or `defthmg` [:doc verify-guards].
- **A `:use`d fact erased by its own rewrite rule**: in a guard proof the
  hypothesis lost its `INTEGERP` conjunct to the rule; keep the fact
  `:rule-classes nil`. A type goal is settled by type reasoning, which never
  calls the rewriter [example: examples/stobjs/nested-stobj.lisp].
- **The guard must itself be guard-safe**: `(declare (xargs :guard (car x)))`
  fails [:doc verify-guards].

Mechanism: every function is a `*1*` executable counterpart and a raw Lisp
definition; once guards are verified the `*1*` checks the guard and calls raw
Lisp [:doc evaluation]. Guard checking is `nil` during proofs and `t` in
`certify-book`/`include-book`; at `:none` raw code runs only for guard `t`
[:doc guard-evaluation-table]. Verification at definition time is attempted
when a `:guard`, type or `:stobjs` is given (eagerness 1, the default)
[:doc set-verify-guards-eagerness]; only `verified` read from the world is an
observation [fn: docs/proofs.md:186-197 @3bbfc4dca]. `(the TYPE EXPR)` and a
type declaration are guard obligations [:doc the], [:doc unsigned-byte-p].
`:guard-debug t` tags each obligation with `(EXTRA-INFO '(:GUARD (:BODY F))
'(CALL ...))`, naming the call it came from [:doc guard-debug]
[example: examples/modelling/guards.lisp]:

```lisp
(verify-guards checksum32-late
  :guard-debug t
  :hints (("Goal" :use ((:instance sum-bytes-bound)))))
```

`ec-call`, `defun-nx`, `mbt` [example: examples/modelling/guards.lisp]:

- `ec-call`: no guard obligation for that call; runs the executable
  counterpart; guard checking stays on [:doc ec-call].

  ```lisp
  (defun reverse-agrees-p (x)
    (declare (xargs :guard t))
    (equal (fast-reverse x nil) (ec-call (spec-reverse x))))
  ```

- `defun-nx`: never runs ("ACL2 cannot ev the call of non-executable
  function"); for specifications and correspondence relations; guards still
  verified as for `defun` [:doc defun-nx].
- `mbt`: `x` in the logic, `t` in raw Lisp, obligation `(equal x t)`; puts a
  guard fact into the termination argument at no run-time cost [:doc mbt]:

  ```lisp
  (defun count-down-to (i n)
    (declare (xargs :guard (and (natp i) (natp n) (<= i n))
                    :measure (nfix (- n i))))
    (if (mbt (and (natp i) (natp n) (<= i n)))
        (if (= i n) 0 (+ 1 (count-down-to (+ 1 i) n)))
      0))
  ```

The guard of a host-called entry runs on every call: a whole-state recognizer
there is a walk per request [fn: docs/proof-style.md:871-879 @3bbfc4dca]
(`ai/05-performance.md` section 1).

## 3. `mbe` and the loop twin

`(mbe :exec e :logic l)` is `l` in the logic and `e` in raw Lisp; the guard
obligation includes `(equal e l)`; `:exec` runs only in guard-verified bodies or
under `:program` code; both sides need the same output signature; the prover
treats it as `:logic` everywhere [:doc mbe].

Pitfalls: with `:verify-guards nil` nothing is claimed about `:exec`; the
`EQUAL` guard goal is at accumulator `NIL` and fails by induction; an `:exec`
under a superior `:logic` is ignored and termination is not checked for it
[:doc defexec].

Shape [example: examples/modelling/mbe-loop-twin.lisp]:

```lisp
(defun keep-evens-loop (xs acc)
  (declare (xargs :guard (and (integer-listp xs) (true-listp acc))))
  (if (consp xs)
      (keep-evens-loop (cdr xs)
                       (if (evenp (car xs)) (cons (car xs) acc) acc))
    (revappend acc nil)))

(defun keep-evens (xs)
  (declare (xargs :guard (integer-listp xs) :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (if (evenp (car xs))
                      (cons (car xs) (keep-evens (cdr xs)))
                    (keep-evens (cdr xs)))
                nil)
       :exec (keep-evens-loop xs nil)))

(defthm keep-evens-loop-is-revappend
  (equal (keep-evens-loop xs acc)
         (revappend acc (keep-evens xs))))

(verify-guards keep-evens)

(in-theory (disable keep-evens-loop))
```

Rules: every later theorem is about the recursion, none about the loop; prove
each loop *shape* once over constrained functions and instantiate (section 15)
[fn: books/def-loop.lisp:14-20 @3bbfc4dca]. An `mbe` twin is safe because
nothing can call its `:logic` at run time; a twin that is a second callable
function is two paths, which is how fn grew "494 hand loop twins and 850
equivalence inductions" [fn: build/coordinator/STRATEGY-20261006.md:266 @worktree 2026-10-28],
[fn: build/coordinator/REPRESENTATION-HISTORY-20261028.md:136 @worktree 2026-10-28].

## 4. `defexec` and fixed-width arithmetic

`defexec`: when the guard is what makes the recursion terminate, it proves the
`:exec` side terminates too [:doc defexec] [example: examples/modelling/defexec.lisp]:

```lisp
(defexec digit-count (n b)
  (declare (xargs :guard (and (natp n) (integerp b) (< 1 b))
                  :measure (nfix n)))
  (mbe :logic (if (and (natp n) (integerp b) (< 1 b))
                  (if (< n b) 1 (+ 1 (digit-count (floor n b) b)))
                0)
       :exec (if (< n b) 1 (+ 1 (digit-count (floor n b) b)))))
```

Fixed width. Pitfall: `unsigned-byte-p` left enabled turns width goals into
inequalities the bit libraries have no rules for; disabled, the rotate's guard
closes with `UNSIGNED-BYTE-P-OF-LOGIOR`/`-LOGHEAD`/`-LOGTAIL` [measured:
`rotl32` of examples/modelling/fixed-width.lisp with and without the disable].
`THE` is a promise to the compiler and a guard obligation [:doc the].
arithmetic-5 was ten times slower than a few fixed-modulus lemmas for base64
[fn: docs/proof-style.md:912 @3bbfc4dca]. Shape
[example: examples/modelling/fixed-width.lisp]:

```lisp
(include-book "centaur/bitops/ihsext-basics" :dir :system)

(local (in-theory (disable unsigned-byte-p)))

(defun rotl32 (x n)
  (declare (type (unsigned-byte 32) x)
           (type (integer 0 31) n))
  (the (unsigned-byte 32)
       (logior (the (unsigned-byte 32) (loghead 32 (ash x n)))
               (the (unsigned-byte 32) (ash x (- n 32))))))

(defthm rotl32-type
  (implies (and (unsigned-byte-p 32 x) (natp n) (< n 32))
           (unsigned-byte-p 32 (rotl32 x n))))
```

Finite properties by bit-blasting: GL `def-gl-thm` with `:g-bindings`
[books: centaur/gl/tutorial.lisp:377-400], FGL `fgl::def-fgl-thm` (needs a SAT
solver) [books: centaur/fgl/doc.lisp:84-91]; neither is certified on the
laptop, so cite their tests (`centaur/fgl/tests.lisp:375-378`).

## 5. `defstobj`

Pitfalls [:doc defstobj], [example: examples/stobjs/array-stobj.lisp]:

- Name clashes with built-ins: `:renaming ((pc get-pc) (update-pc set-pc))`;
  the renaming applies to function names, the updater separately.
- Generated accessors are enabled definitions over `nth`/`update-nth`; prove
  read-over-write while open, then disable them.
- An array field's recognizer is a list recursion: an in-type write needs
  `regsp-of-update-nth` before `machp-of-update-regsi`.
- Element type facts as `:type-prescription` + `:linear`, not a rewrite rule
  concluding `unsigned-byte-p` [example: examples/stobjs/local-stobj.lisp].
- The stobj argument is the stobj variable, never a term: "write `(LET ((ST
  (UPDATE-FIELD1 3 ST))) (FOO ST))`" [:doc stobj].
- A redundant `defstobj` does not reset fields; `:initially` is an object, not
  a form [:doc defstobj].

Shape [example: examples/stobjs/array-stobj.lisp]:

```lisp
(defstobj mach
  (regs :type (array (unsigned-byte 32) (*regs*)) :initially 0)
  (mem  :type (array (unsigned-byte 8) (16)) :initially 0 :resizable t)
  (pc   :type (unsigned-byte 32) :initially 0)
  (seen :type (hash-table eql))
  :renaming ((pc get-pc) (update-pc set-pc))
  :inline t)

(defthm regsi-of-update-regsi
  (implies (and (natp i) (natp j))
           (equal (regsi i (update-regsi j v mach))
                  (if (equal i j) v (regsi i mach)))))

(defthm regsp-of-update-nth
  (implies (and (regsp l) (natp j) (< j (len l)) (unsigned-byte-p 32 v))
           (regsp (update-nth j v l))))

(defthm machp-of-update-regsi
  (implies (and (machp mach)
                (natp j) (< j (regs-length mach))
                (unsigned-byte-p 32 v))
           (machp (update-regsi j v mach))))

(in-theory (disable regsi update-regsi regs-length machp))
```

Names for field `c`: `cP`; scalar `c`/`UPDATE-c`; array `cI`, `UPDATE-cI`,
`c-LENGTH`, `RESIZE-c`; hash table `c-get`, `c-put`, `c-boundp`, `c-get?`,
`c-rem`, `c-count`, `c-clear`, `c-init`; `nameP`, `CREATE-name`; `*c*`
constants show in checkpoints as `(NTH *C* ST)` [:doc defstobj]. A resize is
`RESIZE-LIST`: prove `(len (resize-list lst n default))` first
[example: examples/stobjs/array-stobj.lisp]. `:inline t`, `:non-memoizable t`,
`:non-executable t` and `:congruent-to` are in `ai/05-performance.md`
section 2 and below [:doc defstobj]. "Novices are advised to avoid
`defstobj`" [:doc defstobj]; choose it as a representation decision.

## 6. `with-local-stobj`

Pitfall: the body returns the other values, NOT the stobj
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:26 @worktree 2026-10-28].
Returning it prints "Contrary to the declaration that it is IGNOREd, the
variable HIST is used in the MV-LET expression that binds TOP, N and HIST"
[measured: the first `must-fail` of examples/stobjs/local-stobj.lisp]. "the
body does not even reference `stobj-name`"; illegal at the top level
[:doc with-local-stobj]. A bare multi-value call in `assert-event` needs
`mv-list` [measured: examples/stobjs/local-stobj.lisp drafts]. Shape
[example: examples/stobjs/local-stobj.lisp]:

```lisp
(defstobj hist
  (bins :type (array (unsigned-byte 60) (256)) :initially 0)
  :inline t
  :non-executable t)

(defun most-common-byte (xs)
  (declare (xargs :guard (byte-listp xs)))
  (with-local-stobj
   hist
   (mv-let (top n hist)
     (let ((hist (count-bytes xs hist)))
       (mv-let (top n)
         (most-common-byte-loop 0 0 0 hist)
         (mv top n hist)))
     (mv top n))))

(assert-event
 (equal (mv-list 2 (most-common-byte '(1 2 2 3 2 9 1)))
        '(2 3)))
```

Pitfall for attachable stobjs: a compiled function running `with-local-stobj`
of an attachable stobj, loaded after its attach book, makes certification
illegal (`CHK-ABSSTOBJ-INVARIANTS`), silently at the REPL; query `(@
illegal-to-certify-message)` [cv: ac5fb887#20]. A local stobj allocates per
call (`ai/05-performance.md` section 2).

## 7. Nested stobjs, `stobj-let`, `swap-stobjs`, stobj tables

Stobj-typed fields are read only through `stobj-let` (aliasing)
[:doc nested-stobjs]. Bound variables must be stobj names: three children of
one type need three congruent stobjs ("FEES is not the name of a known
single-threaded object") [measured: first draft of `xfer` in
examples/stobjs/nested-stobj.lisp]. Two producer bindings of one array get an
aliasing guard obligation: put `(not (equal i j))` in the guard
[:doc nested-stobjs]. Shape [example: examples/stobjs/nested-stobj.lisp]:

```lisp
(defstobj acct (bal :type (integer 0 *) :initially 0))
(defstobj acct2 (bal2 :type (integer 0 *) :initially 0) :congruent-to acct)

(defun deposit (i amt bank)
  (declare (xargs :stobjs bank
                  :guard (and (natp i) (< i (accts-length bank)) (natp amt))
                  :guard-hints
                  (("Goal" :use ((:instance bal-type-when-acctp
                                            (a (acctsi i bank)))
                                 nops-type-when-bankp)))))
  (stobj-let
   ((acct (acctsi i bank)))                      ; bindings
   (acct)                                        ; producer variables
   (update-bal (+ amt (bal acct)) acct)          ; producer
   (update-nops (+ 1 (nops bank)) bank)))        ; consumer
```

(`bank` there has `(fees :type acct)`, `(accts :type (array acct (4)))`; `xfer`
binds two elements and the fee child.) `stobj-let` is illegal at the top
level; it clears memo tables of the parent unless `:non-memoizable t`
[:doc nested-stobjs]. `(swap-stobjs st1 st2)` for congruent stobjs; a
`(stobj-table)` field is read as `(stobjs-get 'ctr1 tbl (create-ctr1))` inside
`stobj-let` [:doc swap-stobjs], [:doc stobj-table]
[example: examples/stobjs/swap-and-table.lisp].

## 8. `defabsstobj`

Pitfalls:

- An export updating the foundation twice: "appears capable of modifying the
  foundational stobj, CTR$C, non-atomically; yet :PROTECT T was not specified"
  [measured: examples/stobjs/absstobj-counter.lisp without `:protect t`]. Add
  `:protect t` (slightly slower) or write the one-update-per-branch argument
  beside the export [:doc defabsstobj], [fn: books/octets-stobj.lisp:1167-1170 @3bbfc4dca].
- The event fails and prints every missing `defthm` (`{CORRESPONDENCE}`,
  `{PRESERVED}`, `{GUARD-THM}`); copy them [:doc defabsstobj].
- The recognizer is still a hypothesis of theorems: without `(ctrp ctr)` the
  increment theorem fails at `n = 0` [example: examples/stobjs/absstobj-counter.lisp].
- No supporter of the recognizer or correspondence may have an attachment
  [:doc stobj-attachment-restrictions]; fn hit this through `fn-digest`
  [fn: books/def-representation.lisp:19-28 @3bbfc4dca].
- `:LOGIC` function names are substituted in export guards: use dedicated
  `:logic` functions [:doc defabsstobj].
- Every `:LOGIC` and `:EXEC` function must be guard-verified [:doc defabsstobj].

Obligations, quoted: `{CORRESPONDENCE}` "guarantee that evaluation in the logic
agrees with evaluation using live stobjs"; `{PRESERVED}` "guarantee that
updates to the abstract stobj preserve its recognizer"; `{GUARD-THM}` "if the
`:LOGIC` function's guard holds, then the `:EXEC` function's guard holds"
[:doc defabsstobj]. Shape [example: examples/stobjs/absstobj-counter.lisp]:

```lisp
(defun-nx ctr$corr (ctr$c x)
  (and (equal (ctr$c-val ctr$c) (car x))
       (equal (ctr$c-ops ctr$c) (cdr x))))

(defthm ctr-incr{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (ctr$corr (ctr$c-incr ctr$c) (ctr$a-incr ctr)))
  :rule-classes nil)

(defthm ctr-incr{preserved}
  (implies (ctr$ap ctr) (ctr$ap (ctr$a-incr ctr)))
  :rule-classes nil)

(defabsstobj ctr
  :foundation ctr$c
  :recognizer (ctrp :logic ctr$ap :exec ctr$cp)
  :creator (create-ctr :logic create-ctr$a :exec create-ctr$c)
  :corr-fn ctr$corr
  :exports ((ctr-val :logic ctr$a-val :exec ctr$c-val)
            (ctr-ops :logic ctr$a-ops :exec ctr$c-ops)
            (ctr-incr :logic ctr$a-incr :exec ctr$c-incr :protect t)
            (ctr-reset :logic ctr$a-reset :exec ctr$c-reset :protect t)))
```

(The book proves every obligation for all four exports and the creator.)
Generate the obligations instead of writing them: `defabsstobj-missing-events`
returns `(name formula . old-formula)` triples [:doc defabsstobj-missing-events];
keep the event in a constant so generator and event cannot drift; put the
content in lemmas about the correspondence and disable its recursion first,
or the uniform hint unrolls [example: examples/stobjs/absstobj-generated.lisp]:

```lisp
(defun bset-obligation-thms (missing hints wrld)
  (declare (xargs :mode :program))
  (if (endp missing)
      nil
    (cons `(defthm ,(car (car missing))
             ,(untranslate (cadr (car missing)) t wrld)
             :rule-classes nil
             :hints ,hints)
          (bset-obligation-thms (cdr missing) hints wrld))))

(make-event
 `(make-event
   (er-let* ((missing (defabsstobj-missing-events ,@(cdr *bset-defabsstobj*))))
     (value (cons 'progn
                  (bset-obligation-thms
                   missing
                   '(("Goal" :in-theory (enable bset$corr bset$ap bset$a-mem
                                                bset$a-insert bset$a-card
                                                bset$c-mem bset$c-insert)))
                   (w state)))))))

(make-event *bset-defabsstobj*)
```

Rules from fn's wounds: generate the obligations before the second instance
(285 hand obligations, ~5.8K lines) [fn: build/coordinator/STRATEGY-20261006.md:267 @worktree 2026-10-28];
replace a foundation, never nest the old one inside the new
[fn: books/catalog-paged.lisp:37-50 @3bbfc4dca]; never keep a second
representation beside the abstract one; "Decide up front which representation
owns the held row; do not keep two"
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:12-13 @worktree 2026-10-28].
It pays when one invariant relates several tables to one simple logical value
and nothing served should check it [fn: books/catalog-logic.lisp:4-18 @3bbfc4dca].

## 9. `attach-stobj`

Order and books: implementation stobj, then `attach-stobj`, then the
`:attachable t` `defabsstobj` [paper:
kaufmann2025-acl2-mutable-objects-several-implementations.txt, section 2].
Pitfall: all three in one book passed the first pass and failed at
certification's re-include ("This is supposed to be impossible!") [measured:
`examples/certify.sh stobjs/attach-stobj.lisp` on the one-book version].
Corresponding exports must have the same `:logic` functions [:doc attach-stobj].
Shape, three books [example: examples/stobjs/attach-stobj.lisp]:

```lisp
(include-book "attach-mem-ht")

(attach-stobj mem mem-ht)

(include-book "attach-mem")
```

(`attach-mem.lisp` ends its `defabsstobj mem` with `:attachable t`.) With one
implementation, an ordinary abstract stobj is simpler; fn's
"each attachable generic exists only attached" kept the cost without the
choice [fn: books/history-columns.lisp:13-31 @3bbfc4dca]. Lemma-shape note: a
hash-table correspondence lemma had to be `(equal (equal (cdr
(hons-assoc-equal k alist)) (nth k lst)) t)`, or `lst` is an unbound free
variable [example: examples/stobjs/attach-mem-ht.lisp],
[books: demos/attach-stobj/mem_ht.lisp:73-81].

## 10. Memoization

Only raw Lisp is memoized: guard violations and unverified `:logic` functions
defeat it; not for functions taking `state`, returning stobjs, or constrained
[:doc memoize]. Stobj inputs flush the table on every update, congruent stobjs
included [:doc memoize], [:doc defabsstobj]. Shape
[example: examples/modelling/memoize.lisp]:

```lisp
(memoize 'fib :condition '(> n 10))

(assert-event (equal (fib 90) 2880067194370816120))
```

`(unmemoize 'fib)`, `(clear-memo-table)` [:doc unmemoize]. Fast alists need
`fast-alist-free` [:doc fast-alists].

## Part B: systems

## 11. I/O

`sys-call` "logically returns `nil`", needs a trust tag, and does nothing
during proofs: no theorem can say what it did [:doc sys-call], [:doc defttag].
Channels through `state` exist (`open-output-channel`, `write-byte$`,
`read-byte$`) [:doc io] [example: examples/systems/state-io.lisp]; proving even
"writing keeps a state" needs `std/io/base.lisp`, uncertified on the laptop
[books: std/io/base.lisp:956-993]. fn's choice, the one to copy: effects are
data. "Every effect an instance wants is an ACTION ... the worker's answer is a
COMPLETION ... submission establishes nothing"; a completion matching no
outstanding use "changes nothing and emits nothing"
[fn: books/runtime-contract.lisp:1-10 @3bbfc4dca], [fn: books/runtime-contract.lisp:62-65 @3bbfc4dca].
Every syscall takes its outcome from the environment as an argument
[fn: books/byte-store.lisp:1-14 @3bbfc4dca].

## 12. Crash models

Pitfalls: stating the conclusion as the hypothesis ("That is the right
*conclusion*. It is stated as the *hypothesis*") [fn: specs/crash-model-v2.md:29-35 @3bbfc4dca];
a durability theorem whose hypotheses exclude the crash that breaks a program
missing a fence; `nth`/`update-nth` enabled leaving `(CADR (UPDATE-NTH 1 V (CAR
S)))` unsimplified (disable both; `NTH-UPDATE-NTH` decides reads) [measured:
examples/systems/crash-store.lisp without its disable].

Model as freedoms: pending writes; fsync drains exactly one inode; crash lands
an arbitrary subsequence, each unit `:new`, `:zero` or garbage; failed fsync
lands a torn selection and drops the rest; rename is two operations
[fn: books/byte-store.lisp:1-14 @3bbfc4dca], [fn: books/byte-store.lisp:421-615 @3bbfc4dca].
Shape [example: examples/systems/crash-store.lisp]:

```lisp
(defun land (ws choices)
  (if (atom ws)
      nil
    (let ((w (car ws)) (c (if (consp choices) (car choices) :drop)))
      (cond ((eq c :new) (cons w (land (cdr ws) (cdr choices))))
            ((eq c :zero) (cons (cons (car w) 0) (land (cdr ws) (cdr choices))))
            ((and (consp c) (eq (car c) :garble))
             (cons (cons (car w) (cdr c)) (land (cdr ws) (cdr choices))))
            (t (land (cdr ws) (cdr choices)))))))

(defun crash (s choices)
  (st (apply-writes (st-durable s) (land (st-pending s) choices)) nil))

(defun crash-at (s ops k choices) (crash (run s (take k ops)) choices))

(defthm commit-program-marker-implies-data
  (implies (and (null (st-pending s))
                (not (equal (nth 0 (st-durable s)) 1))
                (member-equal k '(0 1 2 3))
                (committedp (crash-at s (commit-program v) k choices)))
           (equal (nth 1 (st-durable (crash-at s (commit-program v) k choices)))
                  v))
  :hints (("Goal" :in-theory (enable take))))

(assert-event
 (let ((img (crash-at *s0* (commit-program-no-fence 42) 2 '(:drop :new))))
   (and (committedp img) (equal (nth 1 (st-durable img)) 7))))
```

Rules: write down the freedoms the model omits (media corruption, a lying
fence, non-POSIX namespaces, rollback) [fn: specs/crash-model-v2.md:1967-1990 @3bbfc4dca];
flying and unserializable writes [paper: zheng2013-ssd-robustness-under-power-fault.txt, abstract and Table 1];
process death is not power loss [fn: specs/crash-model-v2.md:1934-1935 @3bbfc4dca].
A conservative freedom only makes proofs harder; an omitted one can make them
false on hardware. Tougher models: crash during recovery
[paper: chen2015-fscq-crash-hoare-logic.txt, lines 660-686], metadata-prefix
fsync specs [paper: chen2017-dfscq-verifying-high-performance-crash-safe-fs.txt, abstract],
crash refinement as subset of spec states
[paper: sigurbjarnarson2016-yggdrasil-push-button-crash-refinement.txt, abstract].

## 13. Assumptions, discharged by functional instance

An assumption is an `encapsulate` with a local witness (satisfiable by
construction), a theorem that uses it, and a functional instance that
discharges it; without the last two it is prose [:doc encapsulate],
[fn: books/assumptions.lisp:14-26 @3bbfc4dca], [fn: docs/proofs.md:821-836 @3bbfc4dca].
Pitfall: the constraint is a rewrite rule; its left side must survive to the
goal (with `fsync-ok` or `st-durable` open it never matched) [measured: the
drafts of examples/systems/assumption-instance.lisp]. Shape
[example: examples/systems/assumption-instance.lisp]:

```lisp
(encapsulate
  (((platform-crash * *) => *))
  (local (defun platform-crash (s oracle)
           (declare (ignore oracle))
           (crash s nil)))                    ; the lose-everything image
  (defthm platform-crash-keeps-fenced-view
    (equal (st-durable (platform-crash (fsync-ok s) oracle)) (view s)))
  (defthm platform-crash-keeps-unnamed-blocks
    (implies (and (natp i) (not (names-index-p i (st-pending s))))
             (equal (nth i (st-durable (platform-crash s oracle)))
                    (nth i (st-durable s))))))

(defthm acked-commit-survives-model-crash
  (let ((img (crash (run s (acked-commit-program v)) choices)))
    (and (equal (nth 0 (st-durable img)) 1)
         (equal (nth 1 (st-durable img)) v)))
  :hints (("Goal" :use ((:functional-instance
                         acked-commit-survives-platform-crash
                         (platform-crash (lambda (s oracle) (crash s oracle))))))))
```

A non-platform (zeroing block 1) is refused with "provided we can establish
the two constraints generated", recorded by `must-fail`
[example: examples/systems/assumption-instance.lisp].

## 14. Step functions, invariants, refinement

Pitfalls: a safety theorem is not progress ("Do not describe a safety theorem
as proving inevitable delivery") [fn: docs/proofs.md:71-73 @3bbfc4dca]; an
invariant with no inhabitant proves everything [fn: docs/proofs.md:68-70 @3bbfc4dca];
a fourth outcome that reads as success [fn: docs/proof-style.md:830-835 @3bbfc4dca];
opening a recognizer to prove a transition (1082 subgoals, closed 0.30 s)
[fn: docs/proof-style.md:791-794 @3bbfc4dca]; a refinement about the function
the host does not call [fn: docs/proofs.md:227-231 @3bbfc4dca].

Rules: total step over every event, typed outcomes, refusal is a no-op; one-step
preservation, then trace induction [fn: docs/proofs.md:65-67 @3bbfc4dca]
[example: examples/systems/step-invariant.lisp]:

```lisp
(defthm ob-step-outcome-is-typed
  (member-equal (outcome (ob-step s e)) '(:accepted :refused :uncertain)))

(defthm ob-step-refusal-is-no-op
  (implies (equal (outcome (ob-step s e)) :refused)
           (equal (next (ob-step s e)) s)))

(defthm ob-step-preserves-invp
  (implies (ob-invp s)
           (ob-invp (next (ob-step s e)))))

(defun ob-run (s es)
  (if (atom es) s (ob-run (next (ob-step s (car es))) (cdr es))))

(defthm ob-run-preserves-invp
  (implies (ob-invp s) (ob-invp (ob-run s es))))
```

Prove a dispatcher's keystone with every recognizer closed and the theory
pinned at the form; content at each owning transition
[fn: docs/proof-style.md:760-783 @3bbfc4dca] [example: examples/systems/closed-recognizer.lisp]:

```lisp
(deftheory sess-closed
  '(sessionp phasep line-listp sess-recv sess-close sess-drain))
(in-theory (disable sess-closed))

(defthm sess-step-preserves-sessionp
  (implies (sessionp s) (sessionp (sess-step e s)))
  :hints (("Goal" :in-theory (union-theories
                              '(sess-step sess-recv-preserves-sessionp
                                sess-close-preserves-sessionp
                                sess-drain-preserves-sessionp)
                              (theory 'minimal-theory)))))
```

A whole-state recognizer guards the executable path and is carried, never
recomputed per operation [fn: docs/proof-style.md:269-303 @3bbfc4dca].

Refinement: a keystone with no hypothesis, proved in `minimal-theory` from the
layer below's keystones by `:use` [fn: books/owner-checkpoint-open.lisp:104-121 @3bbfc4dca];
every function guard-verified so it is the program
[example: examples/systems/refinement.lisp]:

```lisp
(defthm replay-from-of-append
  (equal (replay-from s (append xs ys))
         (replay-from (replay-from s xs) ys)))

(defthm recover-from-checkpoint-equals-full-replay
  (equal (recover (capture prefix) suffix)
         (replay (append prefix suffix))))

(defthm recover-encoded-refuses-garbage
  (implies (not (balancesp (decode bytes)))
           (equal (recover-encoded bytes suffix) :refused)))
```

Each rung of the ladder is a refinement about the functions of the rung below
[fn: docs/proofs.md:45-57 @3bbfc4dca]; an abstract stobj is the last rung as
an event [:doc defabsstobj].

## 15. Generic layers by functional instance

Pitfalls: constraints are what every instance owes, so make them the weakest
the generic theorem needs (an identity neutral on all arguments failed for
fixing instances) [measured: examples/systems/generic-fold.lisp with its first
constraints]; disable the executable counterpart of a function over constrained
ones [:doc functional-instantiation-example]; a bad substitution fails with an
ordinary checkpoint, e.g. `(EQUAL (- X) X)` [measured: the `must-fail` of
examples/systems/generic-fold.lisp]. Obligations are the constraints and the
definitions of ancestral functions, under the substitution [:doc constraint].

Shape, one induction for every instance [example: examples/systems/generic-loop.lisp]:

```lisp
(encapsulate
  (((gl-keep *) => *) ((gl-f *) => *))
  (local (defun gl-keep (x) (declare (ignore x)) t))
  (local (defun gl-f (x) x)))

(defthm gl-map-loop-is-revappend
  (equal (gl-map-loop xs acc) (revappend acc (gl-map xs))))

(defthm sq-odds-loop-is-revappend
  (equal (sq-odds-loop xs acc) (revappend acc (sq-odds xs)))
  :hints (("Goal"
           :use ((:functional-instance gl-map-loop-is-revappend
                                       (gl-keep (lambda (x) (oddp x)))
                                       (gl-f (lambda (x) (* x x)))
                                       (gl-map sq-odds)
                                       (gl-map-loop sq-odds-loop)))
           :in-theory (union-theories '(sq-odds sq-odds-loop)
                                      (theory 'minimal-theory)))))
```

The instance's `Rules:` lists only the two definitions: no induction
[measured: `(ld "examples/systems/generic-loop.lisp")`]. `def-functional-instance`
writes the instance theorem for you [books: tools/def-functional-instance.lisp:34-56]
[example: examples/systems/generic-fold.lisp]:

```lisp
(def-functional-instance concat-all-of-append
  mfold-of-append
  ((mop app) (mid (lambda () nil)) (mfold concat-all)))
```

## 16. Teeth and keystones

Pitfalls: green and vacuous (closed-theory corollary, instance corollary,
reflexive conclusion, definition restated, recognizer body, branch of
definition); "The absence of a flag is not evidence of strength. Teeth are"
[fn: docs/proofs.md:199-235 @3bbfc4dca]; a negated `must-fail` is not a
counterexample [fn: docs/proof-style.md:381-383 @3bbfc4dca]; a violating value
outside the guard stops the assertion ("The guard for the function call ...
is violated"), so evaluate it under `with-guard-checking :none` and say so
[measured: the removal-witness draft of examples/modelling/opaque-record.lisp],
[fn: docs/proof-style.md:364-367 @3bbfc4dca].

Rule: "A keystone ships with a reachable non-degenerate witness and one
concrete violating value per hypothesis, each an `assert-event` on the negated
conclusion"; a hypothesis with no violating value is deleted or recorded open
[fn: docs/proof-style.md:349-388 @3bbfc4dca]; plus one mutation a plausible bug
would make. Shape [example: examples/systems/step-invariant.lisp]:

```lisp
(assert-event
 (let ((s (ob-run *s0* '((:put "a")))))
   (and (ob-invp s) (ob-invp (next (ob-step s '(:put "b")))))))

(assert-event
 (let ((bad (ob '("a" "b" "c") 0 nil 2)))
   (and (not (ob-invp bad))
        (not (ob-invp (next (ob-step bad '(:sync :timeout))))))))

(assert-event
 (let ((s (ob '("a" "b") 0 nil 2)))
   (and (ob-invp s)
        (not (ob-invp (next (ob-step-mutant s '(:put "c"))))))))
```

fn's `defteeth` binds teeth to the stored theorem ("TRANSLATED in the current
world and must be EQUAL to `(getpropc NAME 'theorem)`"), takes mutations as
checked edits with a named fault, and leaves `must-fail` off by default
[fn: books/defkeystone.lisp:13-150 @3bbfc4dca]. Non-vacuity is owed at the top
theorems; lemmas earn their keep by use [fn: OWED.md:11-21 @3bbfc4dca].
The statement-first order and the teeth macros: `ai/06-process-and-repl.md`
sections 1 and 2.
