# Lane B: modelling

Read `/Users/ember/dev/acl2aiguide/coordination/COMMON.md` first and obey it.

## Files you own

- `humans/03-modelling-data.md` (data: records, stobjs, abstract stobjs,
  guards, mbe, defexec, fixed-width arithmetic, arrays, local stobjs,
  memoization, nested stobjs)
- `humans/04-modelling-systems.md` (systems: I/O and the OS, crash models,
  state machines and step functions, refinement, functional instantiation
  and generic layers, teeth and keystones)
- `examples/modelling/*.lisp`, `examples/stobjs/*.lisp`, `examples/systems/*.lisp`

## Chapter 3: modelling data

Records: raw lists under an opaque discipline vs `defaggregate`/`fty::defprod`
vs `std::define` with returns; what fn chose and why (fn docs/proof-style.md
sections 1 and 10: `fn-defrecord`, the `-internals` theory, forward-chaining
shape facts, the FTY question). Guards and guard verification: what a guard
is (not a type), `verify-guards`, `:guard-hints`, `guard-debug`, guard
checking modes, `ec-call`, `*1*` functions vs executable counterparts and
what runs raw Lisp (fn docs/proof-style.md section 11: "the executed path
is what counts"), `set-verify-guards-eagerness`, `defun-nx`
[`guard`, `guard-introduction`, `verify-guards`, `guard-debug`,
`guard-evaluation-table`, `ec-call`, `evaluation`]. `mbe`: `:logic` vs
`:exec`, the equality obligation, `mbt`, the loop-twin pattern (a structural
recursion as the logic, an accumulator loop as the exec, bridged by one
lemma) and fn's `def-loop` generalisation of it by functional instance
[`mbe`, `mbt`, fn books/def-loop.lisp header]. `defexec` [`defexec`, books
`defexec/`]. Fixed-width arithmetic: `unsigned-byte-p`, `logand`/`logior`/
`ash`/`loghead`/`logtail`, `the` declarations and fixnums, `ihs` and
`centaur/bitops` lemma libraries, `arithmetic-5` and when a few fixed-modulus
lemmas beat it (fn docs/proof-style.md last lines: base64), FGL and GL for
bit-blasting (what they are, when they pay, `def-gl-thm`/`fgl::def-fgl-thm`
shapes, from `centaur/fgl/doc.lisp` and `centaur/gl/`'s own docs; cite their
test files since the laptop cannot certify them) [`unsigned-byte-p`,
`logops`, `ihs` docs, `bitops` docs, `fgl` docs]. Arrays and single-threaded
objects: `defstobj` (fields, `:type`, `:initially`, `:resizable`, array
fields, hash-table fields `:type (hash-table ...)`), the single-threadedness
syntactic restrictions, `stobj` recognizer and creator, `:inline`,
`:non-memoizable`, `:congruent-to`, stobj-table; `with-local-stobj` and the
exact shape of what the body returns (the lane continuation's hard-won
note: `/Users/ember/dev/fn/build/coordinator/lanedumps/cut-m2a-lb-continuation.md`
"How to run", last bullets); `stobj-let` and nested stobjs; `swap-stobjs`;
`defabsstobj`: the foundation stobj, `:logic`/`:exec` pairs, the
correspondence function `:corr-fn`, the generated obligations exactly as
`defabsstobj-missing-events` prints them ({CREATOR}, {RECOGNIZER},
{CORRESPONDENCE}, {PRESERVED}, {GUARD-THM}), `:protect t` and atomic
update, `:attachable t` and `attach-stobj`; when it pays (fn's catalog: one
correspondence stated once, nothing on a served path revalidates it) and
when it traps you (fn: 285 hand-written obligation blocks, 5,800 lines;
catalog.lisp alone 2,595 lines before generators; the paged catalog
nesting the old foundation whole; `cv search 'defabsstobj-missing-events'`
for the real episodes) [`defstobj`, `stobj`, `with-local-stobj`,
`nested-stobjs`, `stobj-table`, `defabsstobj`, `defabsstobj-missing-events`,
`attach-stobj`, `swap-stobjs`, books `demos/defabsstobj-example-*.lisp`,
`std/stobjs/*`, fn `books/catalog.lisp`, `catalog-logic.lisp`,
`catalog-paged.lisp`, `payload-arena.lisp`, `history-columns.lisp`,
`octets-stobj.lisp`, `msgid-linear-exec.lisp`]. Memoization: `memoize`,
`unmemoize`, `:condition`, `:recursive`, hons and fast alists, when a
memo table is flushed (stobj updates) [`memoize`, `hons`, `fast-alists`,
`hons-and-memoization`, books `demos/memoize-*`].

## Chapter 4: modelling systems

How to model I/O and the OS: `state` and `programming-with-state`,
`io` (channels), `sys-call`, `defttag` and raw Lisp and why they are outside
the logic; the alternative fn took: the host does syscalls, the books decide,
and the OS is a model in the logic (fn `books/byte-store.lisp`: inodes as
octet lists, directories, pending operations, fsync drains, crash lands an
arbitrary subsequence cut into write units that land, land as zeros, or land
as garbage; failed fsync lands a torn selection; every syscall takes an
outcome from the environment; `specs/crash-model-v2.md` on origin/dev) and
where that model is weaker than hardware and real filesystems (no
reordering across fsync of different files? sector atomicity assumptions;
directory fsync semantics; what fsyncgate taught; what a tougher model
looks like from the papers in `~/paperbin` on crash consistency, e.g.
FSCQ/DFSCQ/Yggdrasil/Perennial/"all file systems are not created equal",
if present; `ls -t ~/paperbin`), and how a platform discharges an
assumption by functional instance (fn `docs/proofs.md` "Qualifying a
platform against A-DURABILITY", `books/assumptions.lisp`). State machines
and step functions: `inv(s) /\ permitted(s,e) => inv(step(s,e))`, trace
induction, typed refusals, "a safety theorem is not progress", the
three-outcome rule (accepted / refused / uncertain) [fn docs/proofs.md
"Shape of the claims"]; fn's `deftransition` (`fn-deftransition-closed`,
never open a recognizer to prove a property of a transition, docs/proof-style.md
"Never open a recognizer"); the runtime contract as a machine over a
constrained instance machine (fn `books/runtime-contract.lisp` header).
Refinement proofs: the pattern that worked in fn's recovery refinement
(`books/owner-checkpoint-open.lisp:104`
`fn-owner-recover-from-checkpoint-equals-full-recover`; read the book's
header and the theorem's hints); abstract stobj correspondence as a
refinement; the refinement ladder [fn docs/proofs.md "Refinement ladder"];
what it means that the program the host runs IS the definitions. Functional
instantiation and generic layers: `encapsulate` with constrained functions,
`:functional-instance`, the constraint obligations, `tools/def-functional-instance`,
and fn's `def-loop` (one bridge theorem per shape, every instance by
functional instance, "no instance induction, no instance hint") and
`def-carried` (`-carries`, `-establishes`, `-reaches`; docs/proof-style.md
section 4) [`functional-instantiation`, `functional-instantiation-example`,
`encapsulate`, `constraint`, fn books/def-loop.lisp, books/def-carried.lisp
header]. Teeth: a theorem must have a mutant that bites; the positive
witness, one violating value per hypothesis, `assert-event` on the negated
conclusion, never a general negated `must-fail`, `; teeth: prover-refusal`
labels; keystones and `defteeth`'s `:claim`/`:witness`/`:breaks`/
`:mutations`; the suspect-detector shapes (closed-theory corollary,
reflexive conclusion, definition restated, ...) [fn docs/proof-style.md
section 5, docs/proofs.md "The suspect detector", books/defkeystone.lisp
header, OWED.md header on origin/dev].

## Examples to write and certify

At least: a raw-list record with an opaque discipline (shape, constructor,
accessors by `mbe`, one lemma per field, internals theory disabled); a
guard verification that needs a `:guard-hints`; an `mbe` loop twin with its
bridge lemma; a `defstobj` with an array field and a theorem about its
updater; `with-local-stobj` with an `mv` body; `stobj-let` over a nested
stobj; a complete small `defabsstobj` (a counter or a bounded set) with
every obligation proved and `:protect t` where required; `attach-stobj` of
a second implementation (if it certifies in the laptop's time budget;
`demos/attach-stobj/` shows the shape); `memoize` on a pure function with a
`:condition`; a tiny crash model (a one-file store with pending writes and
a crash that lands a subsequence) with a durability theorem; a step
function with an invariant and a trace-induction theorem plus its teeth
(`assert-event` witnesses); an `encapsulate`d generic fold with one
instance obtained by `:functional-instance`. Each certifies with
`examples/certify.sh`.

## Report

READY with the two chapters, the examples' Built lines, the sources block,
the README lines; or BLOCKED.
