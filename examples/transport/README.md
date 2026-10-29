# Transport experiments A and B

Two one-day experiments from fn2's transport note
[fn: build/coordinator/fn2/TRANSPORT.md:259-321 @worktree, read 2026-10-28],
§4, Experiments A and B. Both are plain ACL2 with no fn2 dependency. Every
book here certifies with `examples/certify.sh transport/<book>.lisp`
(ACL2 8.7, SBCL 2.6.8, laptop), in under 6 s per book.

Experiment B includes `kestrel/apt/propagate-iso`, so it needs APT's
closure certified. The closure is about 160 community books, and it
certified on the laptop in 62 s wall time
[measured: `examples/certify.sh -j 4 .../kestrel/apt/propagate-iso.cert
.../std/util/defiso.cert .../std/util/defmapping.cert
.../std/system/theorem-namep.cert`, ACL2 8.7, laptop, 2026-10-28].

| book | what it holds |
|---|---|
| `fold-contract.lisp` | the generic two-representation contract (`encapsulate`) and `fc-rel-fold`, `fc-obs-fold` |
| `read-state-history.lisp` | read-state as the retained event list; `obs-read`, `obs-count` |
| `read-state-summary.lisp` | read-state as `(hwm . above)`, compacted; admissibility `rs-s-ok`; converter `rs-summarize` |
| `read-state-transport.lisp` | `rs-same-reads`, the per-event-kind lemmas, `rs-summary-adequate` by functional instance, `rs-summarize-related` |
| `read-state-teeth.lisp` | A's negative controls |
| `cursor-v1.lisp` | the v1 cursor row (logical alist view): base functions, users, their theorems |
| `cursor-iso.lisp` | v2 (position split into epoch and seq), `defiso`, the correspondence theorems, `propagate-iso` |
| `cursor-wide.lisp` | B's partiality control: the unrestricted v2 refused |
| `cursor-v3-lossy.lisp` | B's lossy control: v3 without a generation column, refused |

## Experiment A: a fold and its summary, related per event kind

**What it proved.** Summary adequacy has a reusable proof shape, and the
shape is a relation, not an equality of answers.
- `fold-contract.lisp` proves `fc-rel-fold` once, from constraints alone:
  if a relation `fc-rel` holds initially, is preserved by every event, and
  forces the observations to agree, then it holds after every suffix, and
  so do the observations (`fc-obs-fold`)
  [example: examples/transport/fold-contract.lisp].
- For monotone read-state, the relation is `rs-same-reads`, a `defun-sk`
  saying history and summary agree on "is article n read?" for every n.
  The work is one lemma per event kind: `rs-same-reads-of-read`,
  `rs-same-reads-of-catchup`, and `rs-same-reads-of-other` for malformed
  events, which both sides ignore. The summary's half of each lemma
  (`rs-s-obs-read-of-read-step` and its siblings) says how the step moves
  the observation. The count observation is not pointwise. It follows from
  agreement on every article by induction on the bound
  (`rs-obs-count-agree`).
- `rs-summary-adequate` is proved by two `:functional-instance` hints and
  nothing else. From any related, admissible pair, both observations
  (`(:read n)` and `(:count b)`) agree after every suffix of events
  [example: examples/transport/read-state-transport.lisp].
- The converter is a separate obligation, `rs-summarize-related`
  (`(rs-same-reads h (rs-summarize h))`). With adequacy it gives
  `rs-summarize-adequate`: a history and its summary answer every query
  alike, now and after any further events.

**Negative controls** [example: examples/transport/read-state-teeth.lisp]:
- *The relation must be stronger than the observation.* Take the
  observation "count of read articles up to 2". The histories
  `((:read 1))` and `((:read 2))` both give 1. After one more event,
  `(:read 1)`, they give 1 and 2. This is evaluated by `assert-event`, and
  proved as `rs-count2-rel-not-step-closed`. The relation "equal answers
  now" is not closed under the steps.
  `rs-count2-rel-step-obligation-false` proves that the functional
  instance's own step obligation is false at that pair. So the refusal of
  `rs-count2-rel-fold` (a `must-fail` of the functional instance of
  `fc-rel-fold`) is not an automation failure. The stronger relation
  already separates the pair now: it disagrees on article 1.
- *A buggy summary.* `rs-s-bad-step` also advances `hwm` over a gap of one.
  After `(:read 1) (:read 3)` it says article 2 is read, and the history and
  the correct summary say not (`assert-event`).
  `rs-bad-step-breaks-relation` proves that a related pair (the history
  `((:read 1))` and its summary `(1)`) steps to an unrelated one.
  `rs-s-bad-same-reads-of-read` is refused by `must-fail`.

**What it did not show.** Nothing about which past answers storage keeps
available. The theorem is about future observations of the retained
contract (TRANSPORT §4, A, "What it would not show").

**Lines.** About 58 lines of code are the generic contract, written once.
The read-state instance is 43 (history) + 117 (summary, including its
admissibility proofs) + 92 (transport: about 35 lines of per-event-kind
lemmas, 30 lines of functional-instance hints, the observation and
converter lemmas). A second fold over the same contract pays only for its
representations and its per-event-kind lemmas
[measured: `grep -v '^\s*;' FILE | grep -c .`, 2026-10-28].

## Experiment B: column theorems carried by propagate-iso

**What it proved.** The users' theorems about a cursor row can be carried
across a representation change, and the price is the base functions'
correspondence.
- v1 is `((:registration . r) (:position . p) (:generation . g))`, with
  `defcolumns` kinds u32/u60/u60 [fn: fn2/books/columns.lisp @d90b821b3]
  and generation in the role of fn2-pool's `gen`, which rejects a stale
  handle [fn: fn2/books/pool.lisp:46-50 @d90b821b3]. v2 splits the
  position into `(:epoch . e) (:seq . s)`, with position = e * 2^32 + s.
  Both are logical row views (alists), never stobj accessors.
  `propagate-iso` "does not handle mutual recursion" [books:
  kestrel/apt/propagate-iso-doc.lisp], and the logical view is where fn2's
  theorems are stated.
- `apt::propagate-iso` generated 15 events. They are `cur2-advance` and
  `cur2-accepts-token`; the v2 versions of all 9 v1 theorems in the range,
  including the 4 acceptance theorems `cur2-advance-monotone`,
  `cur2-advance-idempotent`, `cur2-advance-rowp` and
  `cur2-advance-keeps-token`, which `theorem-namep` checks exist; and both
  directions of the correspondence theorem for each new function
  (`cur2-advance-is-iso-cur1-advance` and the like). Each comes with its own
  proof. No hint was written for any of them
  [example: examples/transport/cursor-iso.lisp].
- The only hand-written v2 proofs are the 6 correspondence theorems of the
  3 base functions (`cur1-position-->cur2`, `cur2-position-->cur1`, and the
  same for `generation` and `with-position`).

**Hand-written versus generated** (code lines, comments and blanks
excluded, [measured: line count over `cursor-iso.lisp` between its
HAND-WRITTEN markers; generated statements printed from the world at 78
columns, ACL2 8.7, laptop, 2026-10-28]):

| | lines |
|---|---|
| hand-written: v2 recognizer, constructor and base functions | 25 |
| hand-written: the two maps | 11 |
| hand-written: `defiso` and theory events | 6 |
| hand-written: 6 correspondence theorems | 20 |
| hand-written: the `propagate-iso` call | 10 |
| **hand-written total** | **72** |
| generated: 2 functions, 9 carried theorems, 4 correspondence theorems (statements and definitions only) | 71 |
| generated: the full expansion with its proof instructions (`:pcb! :x`) | 1,242 printed lines |
| v1 source the 15 events were generated from (base lemmas, users, their theorems) | 42 |

The pessimistic reading comes first. At this size `propagate-iso` saves
nothing: 72 lines were written to obtain 71 lines of statements. The
hand-written part is fixed per base function, about 15 lines each, and
nearly all of it is mechanical: a v2 accessor and its two correspondence
theorems. The generated part grows with the number of users and their
theorems. So the ratio favours `propagate-iso` when users far outnumber
base functions, and the deferred DSL variant (`defcolumns` emitting the v2
base functions and correspondence theorems from a `:representation-of`
clause) would remove almost all of the hand-written part. The measurement
supports deciding that variant on fn2's real user counts, not on this toy.

**Negative controls:**
- *Partiality: a widened representation is an isomorphism only onto its
  image* [example: examples/transport/cursor-wide.lisp]. `cur2-wide-p`
  admits any u32 epoch. The row with epoch 2^28 and seq 0 is in it, and its
  position is 2^60, which is not a u60. `cur2->cur1` sends it outside
  `cur1-p`. This is proved as `cur2-wide-witness` and
  `cur2-wide-beta-image-false`, as theorems rather than `assert-event`
  because the map's guard is `cur2-p`. The DEFISO `cur1-iso-cur2-wide` is
  refused by `must-fail`. With guard conditions off, the condition that
  fails is `:beta-image`, which was checked in the prover's output.
  Restricting the epoch to u28 (`cur2-p`) makes the image of `cur1->cur2`
  exactly `cur2-p`, and there the isomorphism holds.
- *Dropping the generation breaks stale-token rejection*
  [example: examples/transport/cursor-v3-lossy.lisp]. v3 is
  `((:registration . r) (:position . p))`. `defmapping cur1-to-cur3`
  records the one-way relation: v3 embeds into v1, so `alpha-of-beta`
  holds. The DEFISO `cur1-iso-cur3` is refused by `must-fail` at
  `:beta-of-alpha` (checked in the output), so `propagate-iso` has no
  isomorphism to propagate along. The rows `(7 100 5)` and `(7 100 6)` have
  one v3 image, yet one accepts token 5 and the other rejects it as stale
  (`assert-event`). `no-v3-token-check` proves that an unconstrained
  `cur3-accepts-token` cannot agree with `cur1-accepts-token` on both rows.
  So by functional instantiation no function on v3 rows is a v3 token check.
  The kernel of the lossy map is exactly the identification of generations.

**What the experiment found about the tool**:
- *Domain hypotheses.* A theorem transports only if its hypotheses put the
  row in the isomorphism's domain. `cur1-generation-of-cur1-with-position`,
  stated first without `(cur1-p row)` (it is true without it), made
  `propagate-iso` fail on its v2 version. Stating it under `cur1-p` fixed
  that, and the same was done for `cur1-advance-keeps-token`
  [measured: REPL run of `cursor-iso.lisp`, 2026-10-28; the failure was
  `CUR2-GENERATION-OF-CUR2-WITH-POSITION`].
- *Names come from the predicate.* New names are the old names with the
  domain predicate's name replaced by the codomain's, after a trailing `-P`
  is dropped from both (`string-subst-remove-p` [books:
  kestrel/apt/lift-iso.lisp]). The recognizers are therefore `cur1-p` and
  `cur2-p` (not `cur1-rowp`), so that `cur1-advance-monotone` becomes
  `cur2-advance-monotone`.
- *Correspondence theorems must be disabled.* Stored as enabled rules,
  `cur1-position-->cur2` rewrites `cur1-position` inside `cur1->cur2`'s
  body into a term that contains `cur1->cur2` again, and the next proof
  (`cur1-generation-->cur2`) did not terminate in two minutes. All six are `defthmd`, as in [books:
  kestrel/apt/propagate-iso-test-1.lisp], where the reverse direction is
  `defthmd`.

**What it did not show.** That the logical row corresponds to the served
columns, or that `propagate-iso` scales to fn2's generated accessor
families (TRANSPORT §4, B).

## A pitfall met on the way

A `must-fail` around a functional instance whose substitution was
`(lambda (h q) (declare (ignore q)) ...)` passed, but it passed because
the lambda with a `declare` "is neither a function symbol nor a
pseudo-lambda expression". That is a syntax error, not the refusal being
tested. The teeth book uses a named function instead. Every `must-fail`
here was rerun without the wrapper, and its failure was read. Each one
also sits beside an evaluated witness, or a theorem that its obligation
is false, which is the actual tooth (TRANSPORT §3.1(ii)).
