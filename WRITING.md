# How a chapter of this guide is written

These rules bind every file under `humans/`, `ai/`, `fn-lessons/`,
`assured/` and `examples/`. A chapter that breaks one is sent back.

## Sources, or nothing

1. **No technique is described from memory.** Every mechanism, option,
   keyword, obligation, default or pitfall is read in the ACL2 manual (the
   XDOC source), in a community book, in an fn book, in a paper, or in a
   transcript before it is written down, and the sentence that states it
   carries its source.
2. **Every claim has a source**, in one of these forms. Put the citation
   at the sentence or paragraph it supports. In explanatory chapters, a
   Markdown footnote may hold the full citation; its marker stays beside
   the claim. Keep citations inline in agent chapters so each instruction
   carries its evidence when copied into context.
   - `[:doc TOPIC]` - an ACL2 manual topic (`:doc defabsstobj`). The topic
     name must exist in `books/system/doc/acl2-doc.lisp` or in a community
     book's `defxdoc`.
   - `[books: PATH]` - a community book, path relative to the ACL2 `books/`
     directory (`[books: demos/defabsstobj-example-1.lisp]`), with a line
     number when the claim is about one form.
   - `[fn: PATH:LINE @SHA]` - a file in the fn repository at a pinned sha
     (`[fn: books/catalog.lisp:17 @3bbfc4dca]`). Paths are relative to the fn
     root; the sha is `origin/dev` unless the text says otherwise. fn's
     `build/coordinator/*` documents are untracked (`build/` is ignored), so
     they are cited `[fn: build/coordinator/FILE:LINE @worktree]`, read in
     fn's main worktree on the date the chapter states.
   - `[paper: FILENAME]` - a file in `~/paperbin`, with a page or section.
   - `[cv: SESSION#INDEX]` - a transcript message, as `cv show SESSION
     --around INDEX` finds it.
   - `[example: examples/DIR/FILE.lisp]` - a book in this repository that
     **certified** with `examples/certify.sh` before the citation was written.
   - `[file: PATH:LINE]` - a document on this machine that is neither fn
     nor a paper (`[file: ~/dev/minidregg/CLAUDE.md:18-21]`), quoted, since
     a reader cannot open it.
   - `[guide: PATH:LINE]` - a file in this repository (a chapter, an
     example's README), by path from the repository root.
   - `[fn: commit message of SHA]` - the message of an fn commit, read
     with `git show -s SHA`.
   - `[measured: COMMAND]` - a number this guide's author measured, with the
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

8. Lead with what the reader needs to understand or do. Introduce the
   problem, explain the mechanism, then give the form to copy. Where a
   failure teaches the mechanism, show the failure and its diagnostic.
   Do not make every section begin with a warning: define the concept
   before asking the reader to distinguish it from a misuse.
9. Forms presented for copying are whole and copyable in the stated book
   context. Label illustrative excerpts explicitly and link the complete
   source. Show failed-proof output when the point is how to read it.
10. ASCII only. No emoji. No "simply", "just", "note that". Date and scope
    historical counts; give the generator or command for a current count.
11. `humans/` explains; `ai/` instructs. A section of `ai/` is terse,
    imperative, example-dense, and leads with the pitfall and its fix. It is
    written to be loaded whole into an agent's context.
12. Chapters are rewritten whole when they change. No changelogs, no
    diaries, no "update:" paragraphs.
13. fn is the worked example, not the hero. Where fn did it wrong, say so,
    with the path and sha that shows it, and what the right shape is.

### Write for the reader: the Axios-Dijkstra rule

Make the point easy to find and the argument possible to check. This is
an editorial shorthand, not an external standard.

- State the useful claim before its implementation history. Keep the
  assumptions that make it true in the same paragraph or displayed statement.
- Define a term before using it to explain another term. Explain project
  names such as OWN, G1 and Q1 at first use; retain the names for lookup.
- Give each paragraph one job. Break a long mechanism into its inputs,
  obligations and result when that makes the dependency easier to follow.
- Preserve formulas, hypotheses, examples, counterexamples, measurements,
  limitations and sources. Shorter prose is useful only if it preserves
  their meaning. Move supporting detail to a linked section or footnote
  when it interrupts the explanation.
- Distinguish a specification, a bounded check, an admitted theorem and
  an engineering estimate. Say what each concerns; avoid both overclaiming
  and repeating the same disclaimer after every sentence.
- Prefer a readable repository permalink over a private working-tree
  citation when the texts match. Preserve the old locator in `sources.md`.
- Use descriptive links and headings that tell a reader what they will
  learn. A chapter should make sense without the author's session history.

## Structure

14. `README.md` lists every chapter with one line each; `sources.md` lists
    every source cited anywhere, grouped by kind. Both are kept current by
    the coordinator; a chapter lane reports the sources it added.
15. File names: `humans/NN-topic.md`, `ai/NN-topic.md`,
    `fn-lessons/NN-wound.md`, `examples/topic/name.lisp`.
