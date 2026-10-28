# 08. Whole-state recognizers on the served path

## The wound

Before the 2026-09-19 realignment, whole-state recognizers were "recomputed
on every served operation (`fn-statep` is Theta(n^2) and ran at
`acceptance.lisp:662/695/720`)" [fn: docs/proof-style.md:22-26 @3bbfc4dca].
The measured reason for the rule that followed: "`fn-statep` is Theta(n^2)
in Message-ID comparisons and Theta(n*P) in octet checks, and it ran on every
served operation and four times per replayed record"
[fn: docs/proof-style.md:301-303 @3bbfc4dca].

Fixing the books was not enough, because of how the host calls them: "A
native dispatch `(fnn-core 'f ...)` calls f's executable counterpart, so
**f's guard is evaluated on every call**. A whole-state recognizer in the
guard of a function the host calls is therefore a walk per request. Section
4's "never recomputed" holds only beneath that first call"; and "A function
whose guards are not verified, entered from a counterpart, runs its `*1*`
body. There `mbe` runs `:logic` and every callee's guard is evaluated"
[fn: docs/proof-style.md:873-879 @3bbfc4dca]. The owner's state could not be
moved behind a stobj recognizer either: "`fn-sn-statep` cannot be a stobj
recognizer, so the owner's served entries are guarded by a carried relation
and dispatched raw" (decision D40)
[fn: build/coordinator/scholar-proof-engineering-2026-10-01.md:179-181 @worktree].

## What was done about it

- The `mbe` shape of `docs/proof-style.md` section 4: the recognizer is the
  guard, the `:logic` body keeps the total definition, and the `:exec` path
  skips the test; a caller discharges the callee's guard from a preservation
  keystone; "An entry point checks the recognizer once ... and the loop
  carries it". After it, "the per-operation cost is the operation's own work"
  [fn: docs/proof-style.md:271-304 @3bbfc4dca].
- `def-carried` generates the carrying argument from the world: per
  transition a `NAME-FN-carries` theorem, per open a `NAME-FN-establishes`,
  the bridges, and "It is refused unless each generated statement is proved,
  every declared host entry ... returning the carried stobj is listed, and the
  vacuity probes fail" [fn: docs/proof-style.md:306-320 @3bbfc4dca].
- `tools/hot_path_check.py` in `make check` follows each value that grows
  with retained state "from every `host/` and `host/native/` definition down
  the path that executes" and reports each traversal it reaches, with its
  stated blind spots: path- and context-insensitive, macros unexpanded,
  `equal` taken as constant time; "The tool's silence is not a proof"
  [fn: docs/proof-style.md:856-909 @3bbfc4dca].

## The lesson

A recognizer of the whole state is a theorem's hypothesis and a guard, never
a runtime check on a served path: establish it once at the entry that builds
the state, and prove every transition preserves it. Know which code ACL2
actually runs: in a guard-verified body "only the `:exec` code is evaluated"
[:doc mbe], but a top-level call of a guard-verified function checks its
guard first ("Guards are checked. If the checks pass, evaluation takes place
using the raw Lisp code") [:doc guard-evaluation-table], so the guard of a
function the host calls per request must itself be cheap, and a function
whose guards are not verified evaluates every callee's guard. Plan the
host entry's guard when the state is designed: fn found too late that its
owner state could not be a stobj recognizer and settled for a carried
relation and raw dispatch (D40 above).

## The shape to copy

The recognizer is total (its guard is `t`, since the `:logic` half of the
`mbe` calls it on any value), the transition returns a non-state unchanged in
the logic and skips the test in execution, and a preservation theorem is the
guard proof of the loop [example: examples/fn-lessons/carried-recognizer.lisp]:

```lisp
(defun add-id (id s)
  (declare (xargs :guard (ids-okp s) :verify-guards nil))
  (if (mbe :logic (not (ids-okp s)) :exec nil)
      s
    (if (and (natp id) (not (member-equal id s)))
        (cons id s)
      s)))

(defthm ids-okp-of-add-id
  (implies (ids-okp s)
           (ids-okp (add-id id s))))

(verify-guards add-id)

(defun add-ids (ids s)
  (declare (xargs :guard (and (true-listp ids) (ids-okp s))))
  (if (consp ids)
      (add-ids (cdr ids) (add-id (car ids) s))
    s))
```

fn's own instances are `fn-accept-prepare` and `fn-retain-admissiblep`
[fn: docs/proof-style.md:277-289 @3bbfc4dca]. The entry the host calls per
request then takes a cheap guard (a carried relation, as D40 did), and the
expensive recognizer appears only in theorems and in the one entry that
builds the state.
