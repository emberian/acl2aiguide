# How a chapter of this guide is written

These rules bind every file under `humans/`, `ai/`, `fn-lessons/` and
`examples/`. A chapter that breaks one is sent back.

## Sources, or nothing

1. **No technique is described from memory.** Every mechanism, option,
   keyword, obligation, default or pitfall is read in the ACL2 manual (the
   XDOC source), in a community book, in an fn book, in a paper, or in a
   transcript before it is written down, and the sentence that states it
   carries its source.
2. **Every claim has a source line**, in one of these forms, placed at the
   end of the sentence or paragraph it supports:
   - `[:doc TOPIC]` — an ACL2 manual topic (`:doc defabsstobj`). The topic
     name must exist in `books/system/doc/acl2-doc.lisp` or in a community
     book's `defxdoc`.
   - `[books: PATH]` — a community book, path relative to the ACL2 `books/`
     directory (`[books: demos/defabsstobj-example-1.lisp]`), with a line
     number when the claim is about one form.
   - `[fn: PATH:LINE @SHA]` — a file in the fn repository at a pinned sha
     (`[fn: books/catalog.lisp:17 @3bbfc4dca]`). Paths are relative to the fn
     root; the sha is `origin/dev` unless the text says otherwise. fn's
     `build/coordinator/*` documents are untracked (`build/` is ignored), so
     they are cited `[fn: build/coordinator/FILE:LINE @worktree]`, read in
     fn's main worktree on the date the chapter states.
   - `[paper: FILENAME]` — a file in `~/paperbin`, with a page or section.
   - `[cv: SESSION#INDEX]` — a transcript message, as `cv show SESSION
     --around INDEX` finds it.
   - `[example: examples/DIR/FILE.lisp]` — a book in this repository that
     **certified** with `examples/certify.sh` before the citation was written.
   - `[file: PATH:LINE]` — a document on this machine that is neither fn
     nor a paper (`[file: ~/dev/minidregg/CLAUDE.md:18-21]`), quoted, since
     a reader cannot open it.
   - `[measured: COMMAND]` — a number this guide's author measured, with the
     command that produced it, the ACL2 version, and the machine.
3. **A claim with none of these is deleted**, not hedged.
4. **Quote the manual's words for an obligation or a restriction** (what
   `defabsstobj` requires, what `:protect t` costs, what `with-local-stobj`
   returns). Paraphrase for narrative; never paraphrase a requirement.

## Examples

5. Every technique has a small book under `examples/<topic>/` that
   demonstrates it, with a header comment saying what it shows and which
   chapter cites it. It certifies with `examples/certify.sh <path>` on the
   laptop ACL2 (8.7, SBCL 2.6.8) in well under a minute, and includes only
   community books the laptop has certified (`sources.md`, "Toolchain").
6. A technique whose example cannot certify here in a few minutes (FGL, GL,
   ATC, APT and their closures) is shown by citing the community book's own
   example or test file by path, and the chapter says so.
7. An example that fails to certify is not cited. Fix it or drop the claim.

## Prose

8. Pitfalls first. Each section opens with what goes wrong and how it
   looks in the prover's output, then the mechanism, then the shape to copy.
9. Forms are shown whole and copyable. Show the failed-proof output when
   the point is how to read one.
10. ASCII only. No emoji. No "simply", "just", "note that". No counts that
    will drift; cite the generator or the command instead.
11. `humans/` explains; `ai/` instructs. A section of `ai/` is terse,
    imperative, example-dense, and leads with the pitfall and its fix. It is
    written to be loaded whole into an agent's context.
12. Chapters are rewritten whole when they change. No changelogs, no
    diaries, no "update:" paragraphs.
13. fn is the worked example, not the hero. Where fn did it wrong, say so,
    with the path and sha that shows it, and what the right shape is.

## Structure

14. `README.md` lists every chapter with one line each; `sources.md` lists
    every source cited anywhere, grouped by kind. Both are kept current by
    the coordinator; a chapter lane reports the sources it added.
15. File names: `humans/NN-topic.md`, `ai/NN-topic.md`,
    `fn-lessons/NN-wound.md`, `examples/topic/name.lisp`.
