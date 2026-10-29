# Part 3: assured TigerStyle with ACL2

This part explains how to keep systems rules enforceable as a code base
grows: generate guards and proof obligations from declarations, test the
implementation with independent observations, and reuse proofs when
representations change.

The starting discipline is TigerStyle: bounded work and queues, memory
sized at initialization, assertions that expose internal errors, and
deterministic simulation as an acceptance gate. [Part 1, section 5.7](../humans/05-high-performance.md#57-tigerstyle-in-acl2)
translates those rules into ACL2 one at a time. Here the question is how
to apply them consistently across code written by many authors, including
agents.

The method has five parts, each with a different job:

| Part | What it does | Where to read |
|---|---|---|
| Declarations | Generate storage, guards, bounds and theorem statements from one description | [Chapter 1](humans/01-rules-as-declarations.md) |
| Simulation | Exercise faults and compare independent evidence about bytes, ownership and work | [Chapter 2](humans/02-simulation-and-checkers.md) |
| Commuting squares | State how a representation change or a permitted reordering preserves a named observation | [Chapter 3](humans/03-commuting-squares.md) |
| Proof reuse | Reuse generic arguments and carry clients' theorems across representation changes | [Chapters 4](humans/04-certify-cost.md) and [5](humans/05-transport.md) |
| Metatheory | Prove how local claims compose, with concrete instance obligations still to discharge | [Chapter 6](humans/06-metatheory-split.md) |

Squares organize substitution and reordering claims. Progress, resource
bounds and fidelity to physical devices need their own premises and
arguments. [Chapter 7](humans/07-honest-costs.md) accounts for those limits,
proof status and engineering costs.

## Choose a reading route

For a first read, follow the human chapters in order. For the coherence
and category thread, start with **3, then 5, then 6**, and use 2 and 7 to
check what the experiments establish. Chapter 4 explains the cost of the
proof machinery itself. The chapters introduce the categorical vocabulary
where it becomes useful; they assume familiarity with ACL2 guards, stobjs
and book certification from Part 1.

Agents can load the corresponding instruction chapter for the task at
hand. Each stands alone and keeps its sources inline. The human chapters
put full source locators in footnotes so the explanation can be read
continuously.

| Chapter | Human explanation | Agent instructions |
|---|---|---|
| 1. Rules as declarations | [Bounds, budgets, initialization, ownership and named stops; `defcolumns` and `defmachine`](humans/01-rules-as-declarations.md) | [Generate and check the rules](ai/01-rules-as-declarations.md) |
| 2. Simulation and checkers | [Replay, fault effects, independent evidence and mutation controls](humans/02-simulation-and-checkers.md) | [Build a simulation gate](ai/02-simulation-and-checkers.md) |
| 3. Commuting squares | [G0, G1, G1q and G2; composition premises; the false independence diamond](humans/03-commuting-squares.md) | [State and compose local claims](ai/03-commuting-squares.md) |
| 4. Certification cost | [The one-minute rule, generic templates, pinned theories, splits and the step counter's limit](humans/04-certify-cost.md) | [Keep generated proofs affordable](ai/04-certify-cost.md) |
| 5. Transport | [Functional instantiation, `propagate-iso`, and summary certificates up to congruence](humans/05-transport.md) | [Carry proofs across representations](ai/05-transport.md) |
| 6. The metatheory split | [Lean frame theorems, ACL2 instances, generated presentations and the bridge assumption](humans/06-metatheory-split.md) | [Export and audit the bridge](ai/06-metatheory-split.md) |
| 7. Evidence and costs | [Proved versus owed, measured costs, estimates and limits](humans/07-honest-costs.md) | [Report what the evidence establishes](ai/07-honest-costs.md) |

## The worked system and its evidence

The worked system is **fn2**, the rebuild of the ACL2-based NNTP server fn.
[fn-lessons](../fn-lessons/README.md) records what the earlier design taught.
The main implementation snapshot used here is layer A: the byte pool,
event vocabulary, scheduler and executor, three probe machines, and the
simulator with its checkers. It is pinned to `127f7b877` on fn's historical
`fn2/main` branch. The Lean metatheory is pinned separately to `dddc32d34`
on `fn2/lean-meta`; its generated registry records an older ACL2 source,
`137695dfc`. Chapter 6 explains why those pins must stay distinct.

The guide preserves that implementation snapshot rather than silently
attributing later behavior to it. The later squares experiments are
identified separately: **E1 pass 2** measures search modes and **E2 pass 3**
tests a common declaration form with two consumers, at `d42d18c33`.
Their measured findings appear in chapters 2, 6 and 7.

The design record lives in `fn2/docs/design/`. Where a tracked copy is
byte-identical to a cited coordinator note, the guide uses the public
copy, with the original locator retained in [sources](../sources.md#fn2-part-3-assured).
Private reports retain their dated `@worktree` citations. The review
`REVIEW-SINS-20261028.md` supplies many of the concrete failures; the
chapters distinguish its findings from repairs present at the cited pin.

[The example index](../examples/assured/README.md) maps small certified
books to these chapters. They do not depend on fn2. The transport chapter
also uses [the transport examples](../examples/transport/README.md).
The examples demonstrate individual techniques; the chapters identify
production mechanisms that are supported only by fn2 sources, including
WORK accounting and the process-level acceptance driver.
