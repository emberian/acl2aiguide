# acl2aiguide: continuation

The guide is public at `github.com/emberian/acl2aiguide`. Ember has authorized
editing any content in this repository. Follow `WRITING.md`; the source
inventory and toolchain are in `sources.md`. Keep personal transcripts,
credentials and absolute machine paths out of the public text.

## Present state, 2026-10-29

Parts 1 and 2, `fn-lessons/`, and their executable examples retain their
2026-10-28 content. The root reading guide now points to the revised part 3.

**Part 3, `assured/`, has a reader-focused editorial revision.** Its seven
human chapters introduce concepts before internal names, separate claims
from their premises, and put full source locators in linked footnotes.
Their seven agent companions keep instructions and citations together.
The part's README supplies a reading route through coherence, transport
and metatheory, alongside the complete chapter map.

The writing rule is "make the point easy to find and the argument possible
to check." The Axios-Dijkstra name is an editorial shorthand, not an
external standard. Keep definitions, hypotheses, examples, counterexamples,
measurements, limitations and sources when shortening prose. The rule lives
in `WRITING.md`; the common chapter brief points to it.

The technical distinctions to preserve:

- Squares organize substitution and reordering claims. Progress, resource
  bounds and physical-environment containment need separate arguments.
- The core implementation snapshot remains `127f7b877`; Lean remains
  `dddc32d34`, whose generated registry records ACL2 source `137695dfc`.
- Nine main coordinator notes have byte-identical public copies at
  `fn2/docs/design/` in fn revision `66ff84f4a`. The chapters cite those
  copies; `sources.md` retains the original private locators. Quest and
  continuation reports still have dated `@worktree` references.
- Later evidence is pinned separately at `d42d18c33`: E1 pass 2 shows no
  search advantage for enumeration on its measured workload; E2 pass 3
  supports one declaration form with specialized statement templates.
  Chapter 2 distinguishes the proposed mutations from the six executed
  mutations and the baseline's broader domain from the explicit modes'.
- Prover-step counts understate the relative elapsed cost of the NTH rule
  family. The measurements do not show that every step budget misses it.
  The example's comment was corrected; its executable forms are unchanged.

## Examples and validation

The original part-3 author recorded certification of all 107 example
books from clean on the laptop, ACL2 8.7 / SBCL 2.6.8, on 2026-10-29.
The editorial revision does not claim a fresh certification run.

For this revision, all 82 original fenced code/diagnostic blocks were
compared with the previous revision and preserved. Chapter 5 adds one
observation-triangle diagram. Every original source locator remains
represented, with the public-copy mapping applied. The changed Markdown's
footnotes, local links and pinned Git source targets were checked, and
representative human chapters were rendered for inspection. Only comments
changed in `examples/assured/nth-cost.lisp`; executable forms were compared
unchanged.

The original draft used the coordinator's examples and source checks, with
Astra drafting several human chapters and the agent companions. The current
editor read all part-3 chapters and checked the later E1/E2 reports against
the added text. That is not a new certification or a whole-guide theorem audit.

## Remaining gaps

- `examples/assured/sim.lisp` compares identical replay calls. It does not
  pin a stored fingerprint across edits; both chapters say so.
- No standalone example isolates WORK accounting, missing-execution process
  failure or paired generator-mode replay. Chapter 2 cites fn2 for those.
- `summary-upto.lisp` uses a parity counter, not the proposed read-state
  instance. Chapter 5 names that boundary.
- `owed.lisp` deliberately retains the false `sat-run-monotone` conjecture
  and proves its counterexample at 256. Passing teeth do not prove an owed row.
- The core chapter snapshot has not been refreshed to current fn dev.
  Do not silently replace its counts or findings with later behavior.
- Earlier coverage gaps remain: GL/FGL, ATC, APT beyond `propagate-iso`, FTY
  and `std/io` use community examples; `xdoc::save` has no recipe. The
  `attach-stobj` one-book failure remains a possible upstream report.
