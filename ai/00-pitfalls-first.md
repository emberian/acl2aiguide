# AI 00. Pitfalls first

Load this whole before you touch ACL2. Each pitfall below is one that agents
actually hit in the transcripts of the fn project (an ACL2-verified NNTP
server) and its sibling minidregg, in at least two independent episodes; each
section quotes how ACL2 (or the agent's tool) printed it, says why it happens
in the manual's words, gives the form that fixes it, and cites the episodes as
`[cv: SESSION#INDEX]` (`cv show SESSION --around INDEX` shows the text). The
shapes to copy are in `ai/01-form-shapes.md`; how to run ACL2 and read the
manual is `ai/02-reading-the-manual.md`.

## The ranked list

Ranked by cost: the mean wall-clock of the cited episodes (first symptom to
fix, from the transcript timestamps) times the number of distinct sessions
whose text shows the symptom (from `cv search` and a scan of the matching
sessions). Both are rough. A session count includes sessions that only quote
the message, and for two rows it counts a warning that is often harmless
(marked w); the minutes are those of the episodes cited. Two rows are
silent defects (5 and 8): ACL2 reports nothing, and their real cost is what
was built on them before anyone looked.

| # | pitfall | minutes, cited episodes | sessions | cost |
| ---: | --- | --- | ---: | ---: |
| 1 | "There is no certificate on file": one red read as many | 0.5, 26, 55 | 35 | 950 |
| 2 | A free variable in a rule's hypothesis that never binds | 7, 1 | 131 w | 520 |
| 3 | A step-limited or time-limited probe read as a result | 15, 7, 4 | 50 | 430 |
| 4 | "No induction schemes are suggested" | 3, 0.1 | 268 | 420 |
| 5 | A negated `must-fail` used as teeth: it loops or times out | 105, 21 | 5 | 315 |
| 6 | A `:linear` rule with `:trigger-terms` and no inequality: SBCL memory fault | 98, 110 | 3 | 310 |
| 7 | A whole-state recognizer or a vocabulary opened book-wide; `Time:` not read | 150, 40, 4 | 3 | 195 |
| 8 | A keystone that is vacuous or about the wrong function stays green | 32, 24, 27 | 6 | 170 |
| 9 | `:use` of an enabled rewrite rule | 2.5, 0.2 | 96 w | 130 |
| 10 | A certificate invalidated by copying or touching a book | 10.5, 1 | 20 | 115 |
| 11 | Guard verification refused | 0.3, 0.5, 0.5 | 205 | 90 |
| 12 | A rewrite loop (`Call depth`) | 1, 0.2 | 128 | 75 |
| 13 | A shell timeout, or a load-dependent `Time:`, read as a proof result | 7 | 5 | 35 |
| 14 | Stobj shapes: a local stobj returned, a stobj passed as a term, a multiple value as one | 0.2, 0.1, 0.1 | 176 | 25 |
| 15 | `defabsstobj`: obligations and export guards | 0.5, 5 | 9 | 25 |
| 16 | One form per ACL2 run | 10 | 2 | 20 |
| 17 | Evaluation in a book: guard checking in `assert-event`, `loop$` badges | 0.2, 0.1, 0.1 | 98 | 15 |
| 18 | `defpkg` or a non-local `include-book` inside an `encapsulate` | 9, 0.5 | 3 | 15 |
| 19 | The REPL world is not the certificate (redefinition refused; locals kept) | 0.5, 0.1 | 25 | 12 |
| 20 | Foreground waits on a running ACL2 | seconds (the harness now blocks them) | 6 | under 1 |

Section 21 lists hazards with a single transcript episode each, kept because
the manual states the mechanism and a book here certifies it.

The rules the list comes down to: read the first red, not the cascade; a
probe that was cut off measured nothing; teeth are values, not refusals; a
`:linear` conclusion is an inequality; keep recognizers and vocabularies
closed and read `Time:` first; statement first, with witnesses; certify the
book yourself; batch every run.

---

## 1. "There is no certificate on file": one red read as many

**Symptom.**

```
ACL2 Error in ( INCLUDE-BOOK "history-paged-attach" ...): There is no certificate
on file for ".../spans/books/history-paged-attach.lisp". See :DOC uncertified-books.
This is illegal because we are currently attempting certify-book
```

with a tally like "certified here: passed 166, failed 550"
[cv: agent-a95546f13278495f1#113].

**Mechanism.** "An error will occur if `certify-book` has to deal with any
uncertified book other than the one on which it was called"
[:doc certify-book]; a book that failed leaves no certificate, so every book
that includes it, directly or not, fails with this message
[:doc uncertified-books]. Two other ways to get it: two certifications sharing
one tree, and a cache install replacing certificates mid-run
[cv: agent-a95546f13278495f1#215],
[cv: 01a13b1a-c936-7683-b7be-e1bf70fc022d#256].

**Fix.** Find the red that is not this message, and fix only that:

```sh
# cert.pl leaves BOOK.cert.out beside each book; list the logs with an error
# that is not the cascade message:
grep -L 'There is no certificate on file' $(grep -l 'ACL2 Error' $(find books -name '*.cert.out'))
```
 Never run two
certifications in one tree. fn's triage instrument for a closure with several
independent reds is provisional certification, whose first wave skips proofs
so that every book's proofs run [fn: docs/proofs.md:554 @3bbfc4dca];
"**A triage run is evidence of nothing but its list of reds**"
[fn: docs/proofs.md:588 @3bbfc4dca].

**Episodes.** "All 17 local failures cascade from ONE missing system-book cert
(`std/lists/update-nth`)" -- found in 31 seconds by a lane that looked for the
root [cv: agent-afe5da643499dffa5#531]; 26 minutes and about six probes for a
lane whose run had collided with another worker's certification on the same
tree [cv: agent-a95546f13278495f1#215]; "Only three of the failures were
proofs that didn't go through. The other 262 were books that couldn't
include", after at least 55 minutes of closure runs
[cv: agent-a2b0eec3cd5505ea#508].

## 2. A free variable that never binds

**Symptom.** ACL2 warns when it stores the rule, and the rule then never
fires:

```
ACL2 Warning [Free] in ( DEFTHM FN-B3-WINDOW-TREE-OF-PAIR-TAIL ...): A :REWRITE rule
generated from FN-B3-WINDOW-TREE-OF-PAIR-TAIL contains the free variable U. This
variable will be chosen by searching for an instance of (NATP U) in the context of
the term being rewritten. This is generally a severe restriction on the
applicability of a :REWRITE rule. See :DOC free-variables.
```

[cv: agent-ac9165b0910d94597#70].

**Mechanism.** A variable is free in hypothesis `hi` "if [it does] not occur
in `lhs` or in any `hj` with `j<i`" [:doc free-variables]; it is bound by a
binding hypothesis `(equal var term)`, else by a fact in the context, else by
a ground hypothesis-free rewrite rule [:doc free-variables]. "it is good
practice to put the ``more substantial'' hypotheses first" [:doc
free-variables]; a cheap type hypothesis first binds the variable to the first
match in sight.

**Fix.** Order the hypotheses so the substantial one binds the variable; or
give the binding by hand for one proof with `:use` of an `:instance`, or with
`:restrict`; or prove it as a `:forward-chaining` rule, since "forward chaining
may be indispensable in a scenario with free-variables, whose handling is quite
weak with rewrite rules" [:doc forward-chaining]:

```lisp
:hints (("Goal" :restrict ((subsetp-trans ((y (evens l)))))))
```

[example: examples/prover/by-and-restrict.lisp],
[example: examples/rewriting/free-variables.lisp].

**Episodes.** Seven minutes and five resends: the lane moved the length
equality before `(natp u)` ("Placing the length equality before natp u in the
rewrite rule") [cv: agent-ac9165b0910d94597#72], and closed the proof with two
arithmetic lemmas [cv: agent-ac9165b0910d94597#125]. A sibling lane on the same
theorem family dropped the rule for an explicit `:use` of an `:instance` and
closed at once [cv: agent-a72910f40380df1c2#191].

## 3. A step-limited or time-limited probe read as a result

**Symptom.**

```
ACL2 Error [Step-limit] in STEP-LIMIT: The prover step-limit, which ...
Prover steps counted: More than 3000000
ACL2 Error [Failure] in ( DEFTHM FN-TCL-DRIVE-IS-A-RESULT ...)
```

read as "The forward-chaining addition made it worse -- reverting that"
[cv: agent-a648d33f07c4eb548#619], [cv: agent-a648d33f07c4eb548#622]. Or a
profiler's `SUMMARY time 100.93 seconds ... prover steps 24` read as "closes
too" [cv: agent-ad5b6e0460a5f8ee0#757], [cv: agent-ad5b6e0460a5f8ee0#761].

**Mechanism.** "An `ACL2 Error [Step-limit]` says the form did not finish
inside `n`; it says nothing about whether the form closes, how it splits, or
whether the change under test helped -- and the control run aborts in the same
place for the same reason, so a comparison between them is not a comparison at
all" [fn: docs/proof-style.md:650 @3bbfc4dca]. A step "is counted for each call
of the system functions `rewrite` and `expand-abbreviations`"
[:doc set-prover-step-limit]; a time limit aborts "if ACL2 notices this fact
during a proof" [:doc with-prover-time-limit].

**Fix.** A limit answers only "does this close within `n`": a `yes` is
evidence, a `no` is not. To compare, run without a limit under a wall-clock
`timeout` and read `Time:` and the profile [fn: docs/proof-style.md:666
@3bbfc4dca]. In a book, a limit belongs inside a `must-fail` that records a
deliberate failure, or around a proof that you expect to close:

```lisp
(local (must-fail (with-prover-step-limit 20
                    (defthm app-assoc-probe
                      (equal (app (app x y) z) (app x (app y z)))))))
```

[example: examples/process/step-limit-probe.lisp].

**Episodes.** 15 minutes and a wrongly reverted rule: "**both** of the earlier
probes were invalidated by the 3M step limit I set ... that experiment
measured nothing" [cv: agent-a648d33f07c4eb548#638]; 4 minutes and a claim
that nearly shipped: "The profile was cut by the 4M step limit, not closed --
the tool cannot tell those apart" [cv: agent-ad5b6e0460a5f8ee0#861]; 7 minutes
for a time-limited one: "Form A finished in my probe only because of the step
limit" [cv: agent-ac1aba0aba5e81799#111], the re-probe printing `Time: 45.00
seconds (prove: 45.00, ...)`, which is the 45 s cap and not the proof's cost
[cv: agent-ac1aba0aba5e81799#119].

## 4. "No induction schemes are suggested"

**Symptom.**

```
No induction schemes are suggested by the induction hint.  (Note that
ADT-APPEND-FIELDS (including its :induction rune) is disabled, so it cannot
suggest an induction scheme. Consider providing an :in-theory hint that enables
ADT-APPEND-FIELDS or (:INDUCTION ADT-APPEND-FIELDS).)
```

[cv: agent-a92c068d6d7a309ec#141].

**Mechanism.** A call suggests an induction "only if the controlling actuals
are distinct variables" [:doc induction], and only while its `:induction`
rune is enabled: "Disabling `(:induction fn)` will prevent `fn` from
suggesting the induction scheme" [:doc induction]. Mutually recursive cliques
suggest none [:doc frequently-asked-questions-by-newcomers].

**Fix.** Enable the rune in the hint; give `:induct` a term whose arguments
are variables; or prove the general lemma, after which no induction is needed:

```lisp
(defthm len-of-tk (equal (len (tk n x)) (nfix n)))
```

[example: examples/shapes/hints.lisp], [example:
examples/prover/induct-hint.lisp]. For a clique, `make-flag`
[example: examples/prover/mutual-recursion-flag.lisp].

**Episodes.** Seven seconds when the message named the rune
[cv: agent-a92c068d6d7a309ec#144]; three minutes and four attempts for an
`:induct` hint whose controlling argument was the constant `1`, fixed by
restating the bridge over variables ("`:induct` hints with a constant argument
are being rejected -- the book's own working inductions are all-variable")
[cv: agent-a07bbf9811d425305#241], which is the distinct-variables rule above
applied to the hint's term. Also refused: `:induct` together with
`:use` ("We do not support the use of an :INDUCT hint with a :USE hint")
[cv: agent-ac9165b0910d94597#122], [:doc hints].

## 5. A negated `must-fail` as teeth

**Symptom.** A test book's teeth never finish:

```
HARD ACL2 ERROR [Call depth] in REWRITE:  The call depth limit of 1000
has been exceeded in the ACL2 rewriter.
```

[cv: agent-ac1aba0aba5e81799#42], or the book times out: "`tests/acl2/bp-primary-tests`
... times out (1800 s) in the `must-fail` tooth that drops the item-budget
hypothesis" [cv: agent-a0eaf22c912c1c1fe#39].

**Mechanism.** `(must-fail (defthm h-dropped ...))` succeeds when ACL2 fails
to prove the statement, which is not the same as the statement being false:
"Never a general negated `must-fail`: it proves that the prover could not find
a proof, which is not a counterexample, and it loops when the negation is
unprovable rather than false" [fn: docs/proof-style.md:381 @3bbfc4dca]. By
default `must-fail` counts only soft errors [books:
std/testing/must-fail.lisp:17], so a hard call-depth error inside it is still
an error, and an evidence runner counted it as one
[cv: agent-a0eaf22c912c1c1fe#230].

**Fix.** A concrete violating value, evaluated:

```lisp
(assert-event (let ((x 3) (lo 5) (hi 1))            ; drop the hypothesis ...
                (and (not (clamp-hyps lo hi))
                     (not (clamp-concl x lo hi)))))  ; ... and the conclusion fails
```

[example: examples/shapes/teeth.lisp]. A `must-fail` may sit beside the value,
labelled `; teeth: prover-refusal REASON` [fn: docs/proof-style.md:389
@3bbfc4dca], never instead of it. Outside the guard, evaluate under
`(with-guard-checking :none ...)` [example: examples/process/statement-first.lisp].

**Episodes.** The first lane converted three teeth in 105 minutes and ran out
of budget ("Each is now bitten by a concrete counterexample instead -- an
`assert-event` that evaluates the theorem body on one witness violating the
dropped hypothesis") [cv: agent-ac1aba0aba5e81799#149]; its successor converted
the other twelve in 21 minutes ("Twelve must-fail teeth ... asked the prover
to refute a general statement over free variables. None finished")
[cv: agent-a0eaf22c912c1c1fe#230]. A scheduler cleanup removed "All fifteen
general negated `must-fail` forms" [cv: agent-aecc52e0b9d2f4272#15].

## 6. A `:linear` rule with `:trigger-terms` and no inequality behind it

**Symptom.** The rule is admitted; its first use kills the session:

```
CORRUPTION WARNING in SBCL pid 89337 pthread 0x20042ff80:
Memory fault at 0x15878ead17000004 (pc=0x80076cbe24)
...
Note:  Unhandled memory fault at #x15878EAD17000004.
```

[measured: an `encapsulate` constraining `f` with `(defthm r1 (integerp (f x))
:rule-classes ((:linear :trigger-terms ((f x)))))`, then `(thm (< -1 (f a)))`,
under `timeout 60` in the laptop REPL, ACL2 8.7 / SBCL 2.6.8].

**Mechanism.** The manual: "linear rules are useless when all of the
polynomial's terms are provably non-numeric. If ACL2 determines that to be the
case for one or more of the conclusions, then it causes an error, except when
`:trigger-terms` is supplied explicitly by the user" [:doc linear]. With
`:trigger-terms`, a conclusion like `(integerp (f x))` that yields no
inequality is admitted; an agent traced the fault to that skipped refusal in
`chk-acceptable-linear-rule2` [cv: agent-a074dfcb860a153ca#237]. fn's note on
the same family: "A `:linear` rule with `:trigger-terms` and a `:rewrite` class
on the same conclusion crashed SBCL with a memory fault ... Split it into a type
rule and a plain `:linear` rule" [fn: docs/proof-style.md:911 @3bbfc4dca].

**Fix.** A `:linear` conclusion is an inequality; a type fact is a
`:type-prescription` rule:

```lisp
(defthm cnt-firsts-bound                 ; an inequality: :linear
  (<= (cnt (firsts x)) (cnt x))
  :rule-classes :linear)

(defthm true-listp-of-firsts             ; a type: :type-prescription
  (true-listp (firsts x))
  :rule-classes :type-prescription)
```

[example: examples/shapes/rule-classes.lisp]. If you must have
`:trigger-terms`, make the corollary an inequality, or keep the fact
`:rule-classes nil` and `:use` it, as one lane did after the crash
[cv: agent-ad8a15ee9a85c2c97#411].

**Episodes.** 98 minutes from the fault to a diagnosis and an upstream patch
[cv: agent-a074dfcb860a153ca#85], [cv: agent-a074dfcb860a153ca#237]; a
crash "at its first use, on both boxes" recorded as an obstruction
[cv: agent-abd9b38981b898e07#186]. A related hang: exported `:linear` rules
over a decoder's length terms ("which rewrite the whole decoder on every `len`
term") took 110 minutes to find [cv: agent-a82116ff52db5e71d#305]; the fix
moved their re-enable below the point where the decoders were closed
[cv: agent-a82116ff52db5e71d#332].

## 7. A whole-state recognizer or a vocabulary opened book-wide

**Symptom.** A transition theorem splits into a thousand cases, or a book
times out with the prover idle:

```
Splitter note (see :DOC splitter) for Goal (8844 subgoals).
```

[cv: agent-a648d33f07c4eb548#531];

```
*** Key checkpoint at the top level before a :DO-NOT-INDUCT hint stopped the proof attempt: ***
Subgoal 1082.10' (IMPLIES (AND (FN-TCL-SESSION-SHAPEP S) ...
```

[cv: agent-aaf3093a7caed4a05#23];

```
Time: 2688.15 seconds (prove: 0.02, print: 0.00, other: 2688.13)
```

[cv: agent-a648d33f07c4eb548#702].

**Mechanism.** Enabling a recognizer puts every conjunct into the clause:
"the `(in-theory (enable fn-tcl-sessionp))` above the theorem: opening the
recognizer put its eleven conjuncts ... into the clause and split it into 1082
subgoals" [cv: agent-aaf3093a7caed4a05#78]. A `Time:` line whose `prove` is
near zero is "**not** the rewriter. `other` is where forward chaining and type
reasoning go", and "The cure for that shape is a **theory change, not a
hint**" [fn: docs/proof-style.md:591 @3bbfc4dca]. The library advice: "Most
functions (especially non-recursive function) should be disabled by default"
[:doc best-practices].

**Fix.** Prove transition theorems with the recognizer closed, and open a
vocabulary only in the one hint that needs it:

```lisp
(local (in-theory (disable fn-tcl-sessionp fn-tcl-messagep fn-tcl-step
                           fn-tcl-recv-segment fn-tcl-recv-init
                           fn-tcl-broken-stream)))
```

[cv: agent-a7c235452fee661f6#146] (fn's line). "An includer that needs another
cluster's withdrawn vocabulary enables it in the one `verify-guards` or
`defthm` hint that needs it, never with a book-level `(in-theory (enable
...))`" [fn: docs/proof-style.md:747 @3bbfc4dca]. Read the `Time:` line before
the splitter note; if `prove` is small, profile with `accumulated-persistence`
[:doc accumulated-persistence] and change the theory.

**Episodes.** About 150 minutes, two forty-minute runs and two step-limited
probes before the lane read the `Time:` line ("I lost most of a lane reasoning
about hints and case splits because I read the subgoal count and not that
line") [cv: agent-a648d33f07c4eb548#762]; the book had three configurations
"all three timed out at the 3600 s cap" before the theory was closed at the
top [cv: agent-a7c235452fee661f6#0], after which "C1 went from 0.42 s to 0.05
s" [cv: agent-a7c235452fee661f6#181]. Forty minutes on a recognizer in a
hypothesis: "the form went from 100.93 s and about 10M steps to **0.13 s and
45,658 steps**" once it was closed [cv: agent-ad5b6e0460a5f8ee0#1053]. Four
minutes to diagnose the 1082-subgoal case, about two hours after the failing
certification [cv: agent-aaf3093a7caed4a05#78].

## 8. A keystone that is vacuous or about the wrong function

**Symptom.** None from ACL2: the book is green. The defect is found later, by
an auditor or a refactor: "`fn-cat-ocl-relation-at-recover` is VACUOUS and
`fn-cat-ocl-relation-of-article-finish`'s antecedent is unreachable"
[cv: agent-a7500bdb8c0a49556#60]; keystones "vacuous on a flipped store"
[cv: agent-ad5b12ae974e4c153#28]. A random tester reports success that is not
one: `test?` printed "succeeded" while its verbose run said "Skipping testing
completely, since some functions in this conjecture either take stobj
arguments or are constrained without an attachment"
[cv: agent-a76063db45cd2f3c8#579].

**Mechanism.** The prover proves what it is given. A change of representation
(new arities, a new recognizer) can make an old hypothesis unsatisfiable while
every proof stays green [cv: agent-a7500bdb8c0a49556#60]. A static audit of 377
keystones found 236 sound, 115 missing teeth, 16 about the wrong subject, 10
restating a definition, and none strictly vacuous
[cv: agent-a6a9830e48f770119#513]; its brief opened with "several
restatements were found vacuous only by accident"
[cv: agent-a6a9830e48f770119#0].

**Fix.** Statement first, with a satisfiable witness where the conclusion
fires and one violating value per hypothesis, all `assert-event`s in the book
beside the theorem; the subject is "the function the host calls, or a named
theorem equates them" [fn: AGENTS.md:24 @3bbfc4dca]:

```lisp
(assert-event (let ((x 9) (lo 1) (hi 5))
                (and (clamp-hyps lo hi)
                     (equal (clamp x lo hi) 5)        ; the conclusion fires
                     (clamp-concl x lo hi))))
```

[example: examples/shapes/teeth.lisp], [example:
examples/process/statement-first.lisp]. Do not cite a bare `test?` run: "it
prints "succeeded" when it skipped and "proved" when no example met the
hypotheses" [cv: agent-a8c79a3f8f414058d#18].

**Episodes.** 32 minutes and several farm certifications to restate keystones
"over the function the host calls" [cv: agent-ad5b12ae974e4c153#700]; 24
minutes to the commit and 75 to certified for the catalog relation
[cv: agent-a7500bdb8c0a49556#491]; 27 minutes to rewrite a READY table that
had counted skipped `test?` runs as searches [cv: agent-a76063db45cd2f3c8#659].

## 9. `:use` of an enabled rewrite rule

**Symptom.**

```
ACL2 Warning [Use] in ( DEFTHM FN-CSP-TERMINATOR-JOURNALS-NOTHING ...): It is unusual
to :USE the formula of an enabled :REWRITE or :DEFINITION rule, so you may want to
consider disabling (:REWRITE FN-CSP-RECORD-DONE-JOURNALS-ONLY-SETTLED) in the hint
provided for Goal. See :DOC using-enabled-rules.
```

[cv: agent-a5314b8ab4678de67#115].

**Mechanism.** `:use` adds the instance as a hypothesis, and "these new
hypotheses participate fully in all subsequent rewriting" [:doc hints]: the
enabled rule rewrites its own instance to `T` and the hint does nothing
[example: examples/prover/use-instance.lisp]. The warning is not always fatal:
one lane's proof reached Q.E.D. with it printed
[cv: agent-a3fb7e165b4c64be7#312]; read the `Rules:` line to see whether the
rule fired on its own instance.

**Fix.** Disable the rule in the same hint, or drop the `:use` when the rule
alone does the work:

```lisp
:hints (("Goal" :use ((:instance car-p (x a)) (:instance car-p (x b)))
                :in-theory (disable car-p)))
```

[example: examples/shapes/hints.lisp]. A lemma meant only for `:use` is
`:rule-classes nil` [fn: docs/proof-style.md:242 @3bbfc4dca].

**Episodes.** Three attempts in two and a half minutes, one of which
(`:otf-flg t`) "backfired. Induction exploded to 214k steps", before "The
bridge alone proved the theorem ... Dropping its :use hint should remove the
warning" [cv: agent-a5314b8ab4678de67#129], [cv: agent-a5314b8ab4678de67#141];
a `[Use]` warning followed by a call-depth loop, cured in ten seconds by
disabling the used rule and its partners [cv: agent-a7d460a165ad21de5#645],
[cv: agent-a7d460a165ad21de5#652].

## 10. A certificate invalidated by copying or touching a book

**Symptom.**

```
ACL2 Error in ( INCLUDE-BOOK "acceptance" ...): The certificate for
".../nntp-guards-work/books/acceptance.lisp" lists the book-hash of that book as
((:BOOK-LENGTH . 19852) (:BOOK-WRITE-DATE . 3998706531)). But its book-hash is
now computed to be ((:BOOK-LENGTH . 19852) (:BOOK-WRITE-DATE . 3998719948)).
See :DOC book-hash-mismatch
```

[cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#549]: the same length, a new date.

**Mechanism.** "By default, a book-hash is an alist that records, for a given
book (`.lisp` file), its file size (in bytes) and its write-date"
[:doc book-hash]; the mismatch is "a warning ... which instead will be an error
if this occurs during certification" [:doc book-hash-mismatch]. A copy into
another worktree, a checkout, or a `touch` changes the date.

**Fix.** Hash contents: set `ACL2_BOOK_HASH_ALISTP=NIL` before starting ACL2
[:doc book-hash], as every fn tool does [fn: docs/proofs.md:295 @3bbfc4dca];
key a certificate cache by the book's whole include closure
[fn: docs/proofs.md:308 @3bbfc4dca]. Restoring the dates with `touch -r` is a
patch that the next copy undoes [cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#552].

**Episodes.** A cache found "POISONED -- installed certs do not match the books
they were installed for" [cv: agent-a90a1032ade59e64c#171], 10 minutes from
the first refusal [cv: agent-a90a1032ade59e64c#157] to the rebuilt publisher
"keys entries by the CLOSURE hash" [cv: agent-a90a1032ade59e64c#367]; a session
that restored dates by `touch -r` [cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#552]
met the same refusal again forty and eighty minutes later
[cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#1691],
[cv: 01a0b43d-829f-7551-8d0f-b7af5b836615#2701]. The
dependency form: "its certificate requires the book ".../def-carried.lisp"
with ... book hash 1950127299, but we have included a version of "def-carried"
with ... book-hash 1496597424, so book recertification is probably required"
[cv: 01a11dcf-9b43-79c0-a509-968b82fb9811#348].

## 11. Guard verification refused

**Symptom.**

```
ACL2 Error in ( DEFUN FN-ARP-BYTE ...): The proof of the guard conjecture ...
ACL2 Error [Failure] in ( DEFUN FN-ARP-BYTE ...):
```

with a key checkpoint like `(IMPLIES (AND (FN-ARENA$PP FN-ARENA$P) (NATP P))
(RATIONALP (FN-ARENA$P-NPAGES FN-ARENA$P)))`
[cv: agent-aaac00e0bb3fabe12#270].

**Mechanism.** "Guard verification is intended to guarantee that for any call
of a given function, if its guard holds for that call then the guard will hold
for every function call in the body of that function" [:doc verify-guards].
The checkpoint is a callee's guard that the caller's guard, read through the
rules available, does not imply. Guard hints go in `:guard-hints`; `:hints` are
"to be used during the termination proofs as opposed to the guard verification
proofs" [:doc xargs].

**Fix.** Supply the missing fact once, `:rule-classes nil`, by `:use` in the
one guard proof that needs it; or defer with `:verify-guards nil` and a later
`verify-guards`:

```lisp
(defthm natp-of-sum-nats
  (implies (nat-listp x) (natp (sum-nats x)))
  :rule-classes nil)

(verify-guards sum-nats
  :hints (("Goal" :use ((:instance natp-of-sum-nats (x (cdr x)))))))
```

[example: examples/shapes/defun-guards.lisp]; fn's rule: "An equality that
exists to discharge a guard or an `mbe` obligation is not a rewrite rule. It is
stated once, `:rule-classes nil`, and used by `:use`" [fn:
docs/proof-style.md:242 @3bbfc4dca]. For stobj fields, export the element and
field facts the recognizer would give (a `:forward-chaining` field lemma did it
in the first episode) [cv: agent-aaac00e0bb3fabe12#276],
[example: examples/shapes/stobj-fields.lisp].

**Episodes.** Twenty seconds with a forward-chaining field lemma
[cv: agent-aaac00e0bb3fabe12#276]; two attempts in half a minute, a `:use` in
`:guard-hints` and then a local lemma [cv: agent-a640ab566833bd129#381]; half a
minute lost to a hint in the wrong slot: "I put the catalog proof hint under
`:hints`, which ACL2 treats as a termination hint, instead of `:guard-hints`"
[cv: 01a1311e-ef07-7fd0-aee7-889349162e0c#3300]. A `:use` in a guard hint can
also be rewritten away by its own rule (pitfall 9): "the one failure
was `floor-mod-elim` rewriting away its own `:use` instance"
[cv: agent-a0507c4ff4a5024e3#158].

## 12. A rewrite loop

**Symptom.**

```
HARD ACL2 ERROR [Call depth] in REWRITE:  The call depth limit of 1000
has been exceeded in the ACL2 rewriter.  To see why the limit was exceeded,
first execute
  :brr t
and then try the proof again, and then execute the form (cw-gstack)
```

[example: examples/rewriting/loop-pair.lisp] (the same text in
[cv: agent-a72910f40380df1c2#200]).

**Mechanism.** Two enabled rules rewrite into each other, or a rule rewrites
to an instance of its own left side [:doc rewrite-stack-limit],
[:doc loop-stopper]. When the looping rules are simple abbreviations the loop
is in preprocessing, and `cw-gstack` has nothing to show: "There is no gstack to
print ... this is likely due to the loop ... occurring in so-called
preprocessing ... replaying ... with a hint of: (("Goal" :DO-NOT
'(preprocess)))" [cv: agent-a72910f40380df1c2#216].

**Fix.** Find the pair (`:brr t`, the proof, `(cw-gstack :frames 30)`; or
disable candidates one at a time), keep one direction, and record the choice:

```lisp
(theory-invariant (incompatible (:rewrite f1-is-f2) (:rewrite f2-is-f1))
                  :key f1-f2-direction)
```

[example: examples/rewriting/loop-pair.lisp]; "Sets of rules which are known
to cause rewrite loops should be declared incompatible as a theory-invariant"
[:doc best-practices]. A self-feeding rule takes a `syntaxp` guard
[example: examples/rewriting/syntaxp.lisp].

**Episodes.** About a minute and four probes to bisect it to
`fn-b3-len-of-append` [cv: agent-a72910f40380df1c2#214]; ten seconds to add
the third rule of a loop to the hint's disable list
[cv: agent-a7d460a165ad21de5#652].

## 13. A timeout, or a load-dependent `Time:`, read as a proof result

**Symptom.** A FAILED event whose `Time:` is your own limit: a guard proof cut
by `timeout 120` printed `Time: 119.49 seconds (prove: 0.00, print: 0.00,
other: 119.49)`, "No checkpoints to print" and `FAILED` [measured: the
`bench-stobj` draft of humans/05 section 5.2, laptop REPL]. Or two runs of the
same bytes compared by seconds: "hbox at load 11-22 measured the same bytes at
17 s and 45 s" [cv: agent-a389aedba6c27e180#0].

**Mechanism.** The shell's signal aborts the event like any other failure.
ACL2's own `Time:` "rises with the wall (6.3 vs 14.9 s, same steps)" on a busy
box [cv: agent-a465001fb558f6b6c#34]; prover steps do not, "for fixed bytes and
toolchain the count is the same on any box at any load"
[fn: docs/proofs.md:117 @3bbfc4dca].

**Fix.** Compare by `Prover steps counted:`; treat a FAILED at your own limit
as "did not finish in N", and say so. A process killed at the limit is
`exit=124` from `timeout` [cv: agent-a648d33f07c4eb548#702], which one lane
read correctly: "Probe A finished: killed at 2700 s in C1"
[cv: agent-a648d33f07c4eb548#705].

**Episodes.** The seven-minute time-limit episode of pitfall 3
[cv: agent-ac1aba0aba5e81799#119]; a books-under-contention run that timed out
at 600 s while nine other lane SBCL processes ran, read correctly as
"contention, not a proof failure" [cv: b3f4abb5#517].

## 14. Stobj shapes: a local stobj returned, a stobj passed as a term, a multiple value as one

**Symptom.** Translate errors, each with its own words:

```
ACL2 Error [Translate] in ( DEFUN OBP-BULK ...): The form (FN-OCTETS-APPEND-LIST CUR
FN-OCTETS) is being used as an argument to a call of MV. ... the stobj variable itself
(here, FN-OCTETS) is required, not merely a term that returns such a single-threaded
object.
```

[cv: agent-ad8a376ff7ff84d08#455];

```
ACL2 Error [Translate] in ( DEFUN FN-FEED-LIVE-EFFECTS ...): It is illegal to invoke
FN-FEED-TICK-STEP here because of a signature mismatch. This function call returns a
result of shape (MV * *) where a result of shape * is required.
```

[cv: 01a0c2bc-8b79-7d93-a44f-20361d422ee2#1059];

```
ACL2 Error [Translate] in ( DEFUN FN-OCTETS$CORR ...): A single-threaded object, namely
FN-OCTETS$C, is being used where an ordinary object is expected.
```

[cv: agent-a0d763f0dbe2bbbfc#381];

```
ACL2 Error [Translate] in ASSERT-EVENT: Calls of with-local-stobj, such as
(WITH-LOCAL-STOBJ FN-OCTETS ...), cannot be evaluated directly, as in the top-level
loop.
```

[cv: agent-a0d763f0dbe2bbbfc#864]; and `Illegal with-local-stobj form` /
`Ill-formed with-local-stobj form` when the body is not an `mv-let` of the
right shape [cv: agent-a5acab84669983545#422],
[cv: 01a132b1-740b-70a0-b6de-5ba4aef15406#2461].

**Mechanism.** The `with-local-stobj` body "is a call of `mv-let` that binds
`stobj-name` but does not return `stobj-name`", and the form is not legal
"when typed directly at the top-level loop" [:doc with-local-stobj]. A stobj
argument must be the stobj variable itself. A function of several values is
not a term of one value. Inside a function that declares a stobj, the stobj
cannot be read as a list (`nth`, `equal` against a list).

**Fix.** The shapes, each certified with its wrong twin kept as a `local`
`must-fail` [example: examples/shapes/local-stobj.lisp]:

```lisp
(with-local-stobj scratch                 ; inside a defun, never at top level
  (mv-let (sum scratch)
    (total-and-scratch xs scratch)
    sum))                                 ; return the other values only

(let ((scratch (update-acc 0 scratch)))   ; bind, then pass the variable
  (total-and-scratch xs scratch))

(mv-let (a b) (pair-up x) (declare (ignore b)) a)   ; one value of several
```

`(mv-list 2 (pair-up x))` takes all values where one is wanted in an
`assert-event`; `(mv-nth 1 (pair-up x))` is the reading in theorems. A
correspondence function that reads a stobj as a list is an ordinary function
of two arguments with no `:stobjs` declaration (`defun-nx`)
[cv: agent-a0d763f0dbe2bbbfc#385], [example: examples/shapes/absstobj.lisp].
For a child stobj, the binding form is `stobj-let`, though the message says LET
[example: examples/shapes/stobj-let.lisp].

**Episodes.** Each cost seconds and recurs: in a scan of the sessions the
searches matched, 28 show the top-level `with-local-stobj` refusal, 8 an
illegal or ill-formed `with-local-stobj`, 62 the term-for-a-stobj refusal, 18
the stobj-as-ordinary-object refusal, and about 60 the signature mismatch. Representative
fixes: wrap the `with-local-stobj` in a `defun` and assert on that
[cv: agent-a0d763f0dbe2bbbfc#868]; `(let ((fn-octets (fn-octets-append-list cur
fn-octets))) (mv :ok fn-octets))` [cv: agent-ad8a376ff7ff84d08#457]; `(let*
((answer ...) (fn-lbc ...)) (mv answer fn-lbc))`
[cv: 01a13b94-98f6-7233-ad73-e5eca85a972f#9259]; `mv-nth` in an argument
replaced by `mv-let` [cv: 01a0c2bc-8b79-7d93-a44f-20361d422ee2#1062]. fn's lane
record states the first two as rules
[fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:26 @worktree].

## 15. `defabsstobj`: obligations and export guards

**Symptom.**

```
ACL2 Error in ( DEFABSSTOBJ FN-HIST ...): The following events must be admitted
before the given defabsstobj event is admitted. See :DOC defabsstobj.
(DEFTHM FN-HIST-COUNT{CORRESPONDENCE} (IMPLIES (AND (FN-HIST$CORR FN-HIST$C FN-HIST)
(FN-HIST$AP FN-HIST)) ...
```

[cv: agent-ac7e566206c68920c#327], then

```
At least one guard of an exported function fails to obey single-threadedness
restrictions. See :DOC defabsstobj.
```

[cv: agent-ac7e566206c68920c#340]; and, after editing an obligation by hand,
"[Note discrepancy with existing formula named FN-INPUT-COPY-OPEN{CORRESPONDENCE}"
[cv: 01a0f057-8265-7dd2-b247-ea8131fbaaad#3319].

**Mechanism.** The event checks for theorems of the exact names and formulas
it generates: "Although the `defabsstobj` event will fail if the required
lemmas have not been proved, first it will print the `defthm` forms that must
be admitted" [:doc defabsstobj]. An export's guard is its `:logic` function's
guard with every `:logic` function replaced by its export, and "That guard must
satisfy the usual conditions of a guard: thus, it must return a single
non-stobj value and satisfy normal syntactic restrictions, including
single-threadedness in its handling of stobjs" [:doc defabsstobj]; `(len x)` or
`(+ k x)` of the abstract value in a `:logic` guard uses the stobj as an
ordinary object.

**Fix.** Submit the `defabsstobj` once to get the obligations (or call
`defabsstobj-missing-events` [:doc defabsstobj-missing-events]), copy them
verbatim, prove each under its printed name; write the `:logic` guards through
`:logic` readers of the abstract value:

```lisp
(defun ctr-add$a (k x)
  (declare (xargs :guard (and (natp k) (ctr$ap x) (<= (+ k (ctr-get$a x)) 100))))
  (+ k x))
```

[example: examples/shapes/absstobj.lisp], where the first draft's `(<= (+ k x)
100)` was refused with "A single-threaded object, namely CTR, is being used
where an ordinary object is expected". The agents' own lesson: "Export guards
cannot call `len` on the abstract stobj" [cv: agent-a056258a637cfa703#372].

**Episodes.** Half a minute and two attempts, the second replacing `(< seq (len
fn-hist$a))` by `(< seq (fn-hist$a-count fn-hist$a))`
[cv: agent-ac7e566206c68920c#343]; five minutes and five attempts aligning
hand-written obligations ("ACL2 requires the export obligations in its exact
generated form") [cv: 01a0f057-8265-7dd2-b247-ea8131fbaaad#3322].

## 16. One form per ACL2 run

**Symptom.** A loop of edit, start ACL2, load, try one form, quit. "Each
proof_repl start on hbox takes about 20 to 40 s of sync and install, so
revalidating 23 books took about 10 minutes of waiting"
[cv: agent-a6a9830e48f770119#502]; a tool request: "`probe --form -` refuses
more than one form: accept several (e.g. a helper lemma + the target)"
[cv: agent-a465001fb558f6b6c#0].

**Mechanism.** Each run pays startup, includes and the agent's turn; `ld` on a
list of forms stops at the first error unless `:ld-error-action :continue`
[:doc ld-error-action], so a batch written without it is a one-form run too.

**Fix.** One driver per round: include the certified closure, `ld` every
attempt with `:ld-pre-eval-print t :ld-error-action :continue`, every event
under `with-prover-time-limit`, read the output once, fix everything, run again
[example: examples/shapes/hints.lisp] (its `examples/shapes/driver.lsp`;
`ai/02-reading-the-manual.md` section 6). ember's rule: "iterating across the
whole system and using mental simulations and reasoning in our mind to
metarationally develop without wasteful rerun loops"
[fn: build/coordinator/EMBER.md:392 @worktree].

**Episodes.** The ten minutes above; the lane that cleared twelve teeth used
multi-form drivers [cv: agent-a0eaf22c912c1c1fe#97],
[cv: agent-a0eaf22c912c1c1fe#203].

## 17. Evaluation in a book: guard checking in `assert-event`, `loop$` badges

**Symptom.**

```
ACL2 Error [Evaluation] in ASSERT-EVENT: The guard for the function call (ZP X),
which is (AND (INTEGERP X) (<= 0 X)), is violated by the arguments in the call
(ZP -1).
```

[cv: agent-a4f553c25efb975c0#255]; and

```
ACL2 Error [Translate] in TOP-LEVEL: The body of a LAMBDA object, lambda$ term, or
loop$ statement should be fully badged but FN-LGOC-INVARIANTP and FN-RCON-OCFG-IO are
used in ... and have no badges.
```

[cv: agent-a06a658e1491a12b3#380].

**Mechanism.** Certification runs "as though `(set-guard-checking t)` has been
evaluated" [:doc certify-book], so a teeth form that evaluates a function
outside its guard is a guard violation, not a value. In a `loop$`, "all the function
symbols used in these expressions must be badged (see `defbadge` and
`defwarrant`)" [:doc loop$].

**Fix.** Evaluate an out-of-guard value under `with-guard-checking-event`
(an event form) or `with-guard-checking :none` inside the asserted term, never
a top-level `set-guard-checking` in a book [:doc with-guard-checking-event],
[cv: agent-a6fbb8b530e71afc5#25]; or rewrite the test so its own calls are
guard-clean [cv: agent-aaf7fbd8b1c41d39d#74]. In test books write a plain
recursive helper instead of `loop$` [cv: agent-a06a658e1491a12b3#382]; fn's
lane rule: "`loop$` bodies need badged functions: use plain recursion in test
files" [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:26
@worktree].

**Episodes.** Seconds each: a test rewritten because "assert-event evaluates
its form under guard checking, where the 1- call itself is a guard violation"
[cv: agent-aaf7fbd8b1c41d39d#74]; `(zp k)` replaced by `(equal k 0)` in a test
helper [cv: agent-a4f553c25efb975c0#258]; a `loop$` probe replaced by a
recursive helper [cv: agent-a06a658e1491a12b3#382].

## 18. `defpkg` or a non-local `include-book` inside an `encapsulate`

**Symptom.**

```
ACL2 Error in ( ENCAPSULATE NIL (LOCAL ...) ...): The form (INCLUDE-BOOK
"ihs/quotient-remainder-lemmas" :DIR :SYSTEM) is not an embedded event form in the
context of ENCAPSULATE because we do not permit non-local include-book forms in the
scope of an encapsulate. Consider moving your include-book form outside the
encapsulates, or else making it local. See :DOC embedded-event-form.
```

[cv: 01a0f3b3-a59e-7322-85b8-bb339523ff3f#2508]; and for `defpkg`, "The form
(DEFPKG-FN '"FOO" ...) is not an embedded" event form
[cv: agent-a8f0054be0cd5b5a3#120].

**Mechanism.** `defpkg` is excluded from embedded event forms "because it
affects how things are read" [:doc embedded-event-form], and `defpkg` forms
"should not occur in books" [:doc defpkg]; an `encapsulate` with signatures
forbids non-local `include-book` [:doc encapsulate]. A tool that wraps a book
in `(encapsulate () ...)` to drop its locals (pitfall 19) meets both.

**Fix.** `defpkg` in the book's `.acl2` file, which `cert.pl` runs first
[books: build/doc.lisp:558]; includes at the top of the book, outside any
`encapsulate`, or `local` inside it:

```lisp
; pkg-book.acl2
(in-package "ACL2")
(defpkg "SHAPES" (union-eq *acl2-exports*
                           *common-lisp-symbols-from-main-lisp-package*))
```

[example: examples/shapes/pkg-book.lisp].

**Episodes.** Nine minutes to diagnose and hoist both forms ahead of the
wrapper (`HOISTED_HEADS = ("include-book", "defpkg")`)
[cv: agent-a8f0054be0cd5b5a3#287], a fault that session's handoff says three
lanes hit; another session counts seven [cv: agent-aa9cf89d522b05a7b#344].

## 19. The REPL world is not the certificate

**Symptom.**

```
ACL2 Error in ( DEFTHM ADT-PG-PUT-TREE-IS-PUT-FIELD ...): The name
ADT-PG-PUT-TREE-IS-PUT-FIELD is in use as a theorem. The redefinition feature is
currently off. See :DOC ld-redefinition-action.
```

[cv: agent-aa0987d97e41cae69#143]. For a function, ACL2 also prints both
bodies and keeps the old one: after the refusal, `(f1 3)` returned the old
body's value [measured: `(defun f1 (x) (+ x 1))`, `(defun f1 (x) (+ x 2))`,
`(f1 3)`, laptop REPL].

**Mechanism.** "When `ld-redefinition-action` is `nil`, redefinition is
prohibited" [:doc ld-redefinition-action]. A session loaded form by form also
keeps the `local` events of the books it loaded from source, which an include
of the certified book drops [:doc local]: a dependent "admitted in the REPL
failed certification" [cv: agent-a8f0054be0cd5b5a3#287].

**Fix.** After editing a book, restart the session, or `:ubt` (or `:ubt!`) back
past the first changed event and replay from it [:doc ubt],
[cv: agent-aa0987d97e41cae69#146]. Load dependencies as certified includes,
not from source. Certify the changed book before you report: "A form ACL2
admits there is not a certificate" [fn: docs/proofs.md:506 @3bbfc4dca].

**Episodes.** Under a minute each, but about 25 sessions show the refusal
(query `ld-redefinition-action`): a theorem renamed with a `-nil` suffix to get
past it [cv: 01a1331b-f74c-7370-b457-26d6f06c771a#1001]; `ubt!` then a replay,
which sometimes left the session missing an earlier `defun`
[cv: agent-aa9cf89d522b05a7b#644]. The source-loaded locals case cost a
certification red and a tool change [cv: agent-a8f0054be0cd5b5a3#287].

## 20. Foreground waits on a running ACL2

**Symptom.** The harness now refuses them:

```
<tool_use_error>Blocked: sleep 120 followed by: cat .../tasks/bxoedhs1w.output.
To wait for a condition, use Monitor with an until-loop
```

[cv: agent-ad74d6f4191264730#255]; again with `sleep 110` and `sleep 60` in
another lane [cv: agent-a8c9cefa3ba9a6f9d#66].

**Mechanism and cost.** Before the block, fn's process audit measured two
integrator seats spending "5.4 h of 10.4 h in 77 calls over 60 s (most of them
`until grep ... ; do sleep 15` loops ...)" [fn:
build/coordinator/PROCESS-AUDIT-20261009.md:66 @worktree].

**Fix.** Run anything longer than a tool call's limit in the background with
a PID file, wait on its completion with one background monitor, and work in
the meantime [fn: build/coordinator/lanedumps/cut-m2a-lb-continuation.md:25
@worktree]. A job started with a trailing `&` inside the agent's shell can die
with the turn: "a certification started with a trailing `&` inside your shell
is killed by SIGTERM when your turn ends" [cv: b3f4abb5#556].

## 21. Hazards with one transcript episode

Kept because the manual states the mechanism and a book here certifies it;
each is an anecdote in the transcripts, not a measured recurrence.

- **A `Goal` `:in-theory` lost under a subgoal hint.** "This call of the
  `enable` macro enables `g` relative to the `current-theory` of the current
  logical world, *not* relative to the theory produced by the hint at `Goal`"
  [:doc hints]. fn's tcpcl-invariants lane found its own `Goal` disable undone
  by `("Subgoal *1/3" :in-theory (enable fn-tcl-drive-is-a-result))`
  [cv: agent-a7c235452fee661f6#146]; an audit found two more such sites, both
  unmeasured [cv: agent-a80c4b5d2db4522d4#23]. Spell the whole `e/d` at each
  subgoal [example: examples/shapes/hints.lisp],
  [example: examples/prover/subgoal-theory.lisp].
- **Restarting from a summary instead of resuming the agent.** A fresh agent
  re-ran probes and re-found the call-depth errors its predecessor had located
  two hours earlier [cv: agent-a0eaf22c912c1c1fe#195],
  [cv: agent-ac1aba0aba5e81799#42]. fn's audit target: "5 successions ...,
  each from the predecessor's own continuation file ... no lost thread found"
  [fn: build/coordinator/PROCESS-AUDIT-20261009.md:12 @worktree].
- **`minimal-theory` as a reflex.** A tree audit counted "116 hints reach for
  `minimal-theory`/`union-theories` (lanes fighting the inherited rule set)"
  [cv: 8d4521d3-3e8f-4a05-a722-a9c843463a45#1969]; "A lane that reaches for
  `minimal-theory` instead has skipped this step" (profiling)
  [fn: docs/proof-style.md:588 @3bbfc4dca]. A deliberate `minimal-theory`
  inside a generator then needed `nfix` and its type facts added back one at
  a time [cv: agent-ae2f97821f3cd5fd#684].
- **`skip-proofs` in a book that must certify.** No transcript episode found;
  the manual: "The value `nil` causes an error if such an event is found"
  (`:skip-proofs-okp` of `certify-book`) [:doc certify-book], and `cert.pl`'s
  default `(certify-book "foo" ? t)` does not allow it
  [books: build/doc.lisp:673].
