# Common brief for every acl2aiguide chapter lane

You are an Opus chapter writer for `~/dev/acl2aiguide`, a guide to
ACL2 for humans and for AIs. Read, in this order, before writing anything:

1. `~/dev/acl2aiguide/WRITING.md` (the rules; every claim has a
   source line; no technique from memory).
2. `~/dev/acl2aiguide/README.md` and `sources.md`.
3. Your lane brief (the file that pointed you here).
4. The manual topics and the fn files your lane brief names, **whole**, before
   writing the section that uses them.

## The material and how to read it

**The ACL2 manual (XDOC).** ACL2 8.7's manual source is
`~/tools/acl2-fn/acl2-8.7/books/system/doc/acl2-doc.lisp`
(175,049 lines; one `(defxdoc TOPIC ...)` per topic). To read a topic:

    D=~/tools/acl2-fn/acl2-8.7/books/system/doc/acl2-doc.lisp
    grep -n '^(defxdoc defabsstobj$' $D        # find the start line
    grep -n '^(defxdoc ' $D | awk -F: '$1 > START' | head -1   # the next topic = the end
    sed -n 'START,ENDp' $D

or render it with the REPL (0.2 s startup; strip the colour codes):

    printf ':doc defabsstobj\n' | ~/tools/acl2-fn/acl2-literal-4g-tls64k 2>&1 | sed 's/\x1b\[[0-9;]*m//g'

Community-book topics are `defxdoc` forms in the books themselves:
`grep -rn '(defxdoc fgl$' ~/tools/acl2-fn/acl2-8.7/books/centaur/fgl/`.
`doc/practices.lisp` holds `best-practices`, `theory-management`,
`conventional-normal-forms`, `finite-reasoning`, `working-with-packages`.
Topic names you will need exist under these exact names in `acl2-doc.lisp`:
`introduction-to-the-theorem-prover`, `the-method`, `acl2-tutorial`,
`hints`, `hints-and-the-waterfall`, `induction`, `rewrite`, `loop-stopper`,
`free-variables` (and `free-variables-examples-*`), `forward-chaining`,
`type-prescription`, `linear`, `theories`, `enable`, `disable`, `in-theory`,
`local`, `encapsulate`, `include-book`, `certify-book`, `books`,
`functional-instantiation`, `functional-instantiation-example`,
`skip-proofs`, `defattach`, `break-rewrite`, `accumulated-persistence`,
`dmr`, `pstack`, `with-prover-time-limit`, `set-gag-mode`, `proof-builder`,
`stobj`, `defstobj`, `defabsstobj`, `defabsstobj-missing-events`,
`attach-stobj`, `with-local-stobj`, `nested-stobjs` (covers `stobj-let`),
`stobj-table`, `memoize`, `defexec`, `mbe`, `guard`, `guard-introduction`,
`verify-guards`, `guard-debug`, `ec-call`, `arrays`, `hons`, `fast-alists`,
`with-fast-alist`, `defun-sk`, `defchoose`, `defun-nx`, `meta`, `bind-free`,
`syntaxp`, `case-split`, `backchain-limit`, `set-default-hints`,
`tau-system`, `make-event`, `assert-event`, `provisional-certification`,
`programming-with-state`, `io`, `profile`, `comp`, `defpkg`. Check any other
name with `grep -c '^(defxdoc NAME$'` before citing it; `loop$`, `apply$` and
`checkpoint` topics exist under names you must look up.

**The community books** are at `~/tools/acl2-fn/acl2-8.7/books`.
Worth knowing: `demos/defabsstobj-example-{1,2,3,4-book,5}.lisp`,
`demos/attach-stobj/`, `demos/stobj-table-examples.lisp`,
`demos/swap-stobj-fields.lisp`, `demos/memoize-*.lisp`, `demos/loop-primer/`,
`std/stobjs/{absstobjs,nested-stobjs,1d-arr,bitarr,clone,stobj-table,
updater-independence}.lisp`, `centaur/fgl/{doc,top}.lisp`,
`centaur/bitops/`, `kestrel/c/atc/{doc,tutorial}.lisp` and
`kestrel/c/atc/tests/*.lisp` (each with its generated `.c`),
`kestrel/apt/{doc,*-doc}.lisp` and `*-tests.lisp`, `proofstyles/`,
`arithmetic-5/`, `std/lists/`, `tools/def-functional-instance.lisp`,
`tools/flag.lisp`, `std/util/define.lisp`, `std/testing/must-fail.lisp`.

**fn** is at `~/dev/fn` (main worktree; read, never edit; use
`git -C ~/dev/fn show origin/dev:PATH` for the pinned text and
cite `@3bbfc4dca`). Its practice docs: `docs/proof-style.md` (912 lines:
opaque records, export theory at book end, `:rule-classes nil` guard
equalities, carried invariants, teeth as concrete witnesses, book layering,
what may leave a book enabled, profiling with `accumulated-persistence`, the
`Time:` line, step limits, `Goal` `:in-theory` not surviving subgoal hints,
never enabling a vocabulary book-wide, never opening a recognizer),
`docs/proofs.md` (876 lines: refinement ladder, shape of claims, trust and
executable efficiency, the ledger, guard status, the suspect detector, cert
cache and `ACL2_BOOK_HASH_ALISTP=NIL`, `proof_repl.py`, provisional
certification for triage, A-DURABILITY by functional instance),
`docs/resource-contract.md`. Generators and models: `books/def-loop.lisp`
(functional-instance layering of loop twins), `books/definterface.lisp`,
`books/defkeystone.lisp` (`defteeth`), `books/catalog.lisp` +
`catalog-logic.lisp` + `catalog-paged.lisp` (the `defabsstobj` catalog, an
attachable generic, the paged implementation), `books/byte-store.lisp` (the
crash model) and `books/byte-store-*.lisp`, `books/runtime-contract*.lisp`
(the executor/action/completion layer over a constrained machine),
`books/msgid-linear-exec.lisp` (stobj page table, fixnum words, measured
consing), `books/payload-arena.lisp` (attachable arena with handles),
`books/history-columns.lisp` (a 155-line attachable generic),
`books/octets-stobj.lisp` (`fn-octets`, the octet buffer),
`books/owner-checkpoint-open.lisp:104`
(`fn-owner-recover-from-checkpoint-equals-full-recover`, the recovery
refinement), `books/assumptions.lisp` (named assumptions as encapsulates),
`OWED.md` (the keystone/teeth convention, on `origin/dev`). The lessons:
`build/coordinator/ANATOMY-20261009.md` (the three sins),
`PROCESS-AUDIT-20261009.md`, `AUDIT-TWO-WEEKS-20261013.md`, `EMBER.md`
(ember's words; sections "Cut, drain, collapse" and "Assurance"),
`RULINGS.md`, `CUT-M2-PLAN-20261027.md`,
`lanedumps/cut-m2a-lb-continuation.md`,
`REPRESENTATION-HISTORY-20261028.md`.

**Papers** are in `~/paperbin` (`ls -t ~/paperbin | head -40`; another agent
is adding proof-automation, program-logic, crash-model and code-generation
papers now, so look again before you finish). Read the `.txt`.

**Transcripts.** `cv search '<term>'` finds how real ACL2 work went across
every agent transcript on this machine (`cv search 'defabsstobj'`,
`cv search 'with-local-stobj'`, `cv search 'functional-instance'`,
`cv search 'skip-proofs'`, `cv search 'Step-limit'`, `cv search 'free variable'`);
`cv show <id> --around N` reads one. Cite as `[cv: ID#N]`.

## Examples

Every technique you describe gets a small book under
`~/dev/acl2aiguide/examples/<topic>/<name>.lisp` with a header
comment (what it shows; which chapter cites it). Certify it:

    cd ~/dev/acl2aiguide && examples/certify.sh <topic>/<name>.lisp

That runs `cert.pl` with the laptop ACL2 under a machine-wide lock (one
certification at a time; it waits for other lanes). A book must certify in
well under a minute and may `include-book` only the community books listed in
`sources.md` "Toolchain" as certified on the laptop (`std/lists/*`,
`arithmetic-5/top`, `std/util/define`, `std/testing/must-fail`, `tools/flag`,
...). For a fast scratch loop, pipe forms into the REPL under a timeout:

    timeout 120 ~/tools/acl2-fn/acl2-literal-4g-tls64k < scratch.lsp > out.txt 2>&1

and read `out.txt` once; the REPL starts in 0.2 s, so batch many forms per
run and never loop one form at a time. Keep scratch files under your own
scratchpad directory, not the repository. An example that does not certify
is not cited. FGL, GL, ATC and APT are not certified on the laptop and their
closures take too long: for those, cite the community book's own test file by
path and say the example is theirs.

## Writing

`WRITING.md` is the contract. Lead with the reader's problem and the useful
claim; use failure-first explanations where they teach the mechanism.
Every claim has a source, inline or in a footnote; quote the manual for an obligation;
show forms whole; show prover output when the point is reading it; ASCII,
no emoji; `humans/` explains, `ai/` instructs; fn is the worked example and
its failures are named with path and sha. Let the explanation determine
length: preserve the definitions, assumptions, examples and limits without
padding or skipping difficult material. Write each chapter whole into its file; if you revise,
rewrite the file whole (no appended "update" paragraphs).

## What you deliver

- Your chapter files, whole, at the paths your lane brief names.
- Your example books, certified, with the `cert.pl` "Built ... .cert" line
  for each in your report.
- A sources block in your report: every `[:doc]`, `[books:]`, `[fn:]`,
  `[paper:]`, `[cv:]` and `[measured:]` you cited, one per line, so the
  coordinator can fold it into `sources.md`.
- One line per chapter for `README.md`.

Do NOT commit; do NOT edit `README.md` or `sources.md` (the coordinator
does); do NOT touch another lane's files. Write only your own files.

## Rules (verbatim, from the owner)

- Never kill a process by pattern. No `pkill -f <anything>`, no `pkill -x`,
  no `killall`, no `kill -u`. A process you started is stopped by the PID in
  its PID file, and only that. No PID file, no kill: say so instead.
- Never `git stash`; never `git add -A`; do not commit in this repository.
- Nothing runs on hbox or any remote box. The ACL2 you run is the laptop's,
  through `examples/certify.sh` or the launcher above, one certification at
  a time, nothing over a few minutes of CPU. Use `timeout` on every REPL run.
- No secrets in the repository (no keys, no tokens, no hostnames with
  credentials).
- Disk pressure is a pause-and-tell condition, never a delete.
- Do not edit anything under `~/dev/fn`.

## Reporting

Your final message is the report: READY (chapters written, examples
certified with their Built lines, the sources block, the README lines, and
anything you could not source and therefore left out) or BLOCKED (what, why,
what you need). Keep it to what the coordinator needs; the coordinator reads
your files, not a summary of them.
