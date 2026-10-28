# acl2aiguide

A guide to ACL2 for humans and for AIs: the logic and the prover, how proofs
fail and how to read them, modelling (records, stobjs, abstract stobjs, guards,
`mbe`, fixed-width arithmetic, I/O and crash models, state machines,
refinement, functional instantiation), high-performance software in ACL2 (the
executable/logical split, static allocation, no consing on hot paths, code
generation), the process that gets assurance without drowning in it, and, for
agents, the pitfalls first.

It is written from the ACL2 manual and community books (ACL2 8.7), from the fn
project (an ACL2-verified NNTP server, two years and about 1,400 books, now
being rebuilt as fn2), from papers, and from the transcripts of the agents that
did the work. Every claim carries a source line (`WRITING.md`). Every example
under `examples/` certifies on a laptop ACL2.

## How to read it

- **Humans** start at `humans/01-logic-and-prover.md` and read in order.
- **Agents** load `ai/00-pitfalls-first.md` and `ai/01-form-shapes.md` into
  context before touching ACL2, then the `ai/` chapter for the task at hand.
- **fn2 builders** read `fn-lessons/` first: what fn taught, by wound, each
  with the path and sha that shows it.
- `examples/` are small certified books, one per technique; `make -C
  examples` certifies them all with the laptop's ACL2.
- `sources.md` is every reference: manual topics by name, community books by
  path, fn books by path and sha, papers by filename, transcripts by id.

## Chapters

### Part 1: for humans (`humans/`)

- `humans/01-logic-and-prover.md`: the logic (total functions over five data
  types, `:logic`/`:program`), definitions and termination, induction, the
  waterfall, how to read a failed proof, the debugging tools, every hint with
  a failing-then-fixed example, induction schemes, step limits,
  `skip-proofs`/`defaxiom`/trust tags.
- `humans/02-rewriting-theories-books.md`: how rules are made and used, free
  variables, loops, every rule class, normal forms, theories, `local` and what
  a book exports (`encapsulate`, functional instances, `defattach`), books and
  certification (`cert.pl`, book hashes, provisional certification,
  `make-event`, `must-fail`), with fn as the worked example.
- `humans/03-modelling-data.md`: modelling data: opaque records, guards and
  `*1*` execution, `mbe` loop twins, `defexec`, fixed-width arithmetic,
  stobjs (concrete, local, nested, abstract, attachable), memoization, with
  fn's representation wounds.
- `humans/04-modelling-systems.md`: modelling systems: I/O outside and
  inside the logic, crash models and their gaps against hardware,
  assumptions discharged by functional instance, step functions and trace
  induction, refinement, generic layers, teeth and keystones.
- `humans/05-high-performance.md`: what runs when (`*1*` vs raw, `mbe`,
  `:program`), fixed-size stobjs, finding the consing (`time$`,
  `profile`/`memsum`), fn's octet-list lesson, group commit and one executor
  loop as modelled state, TigerStyle translated, ATC/APT against fn's
  extraction, and what generating macros buy and cost.
- `humans/06-process.md`: statement first and teeth, what to prove early and
  late, keeping checkers and ledgers small, sizing proofs (steps ratchet,
  800-line split, include cost, one world), honest skip-proofs, running ACL2
  from an agent, and fn's process audit as rules.

### Part 2: for AIs (`ai/`)

(chapters are listed here as they land)

### fn lessons (`fn-lessons/`)

(lessons are listed here as they land)

## How to cite it

Cite a chapter by path and heading, e.g. `acl2aiguide humans/03-modelling-data.md
"Abstract stobjs"`. Cite an example by its path. The guide's own sources are
in `sources.md`; cite those directly when the claim is theirs.

## Toolchain

ACL2 8.7 on SBCL 2.6.8 (`~/tools/acl2-fn/acl2-literal-4g-tls64k`, built by
`~/dev/fn/tools/build_local_acl2.sh`; community books at
`~/tools/acl2-fn/acl2-8.7/books`). `examples/certify.sh` runs `cert.pl` with
that ACL2, one certification at a time.
