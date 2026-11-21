# Math Inc: "Abstraction considered helpful" and the sphere-packing report (Gauss)

| Field | Value |
|---|---|
| Authors, organisation | Math, Inc. The position piece is signed by Dhruv Makwana, member of technical staff. The other two posts are unsigned |
| Date and version read | Pages as they were on 21 November 2026. The pages carry no date. The position piece is blog post number 7, the newest of seven; it cites sources of 2026 [U for the exact date]. The sphere-packing post gives "February 2026" for the result |
| Source | Not a paper. Company blog: https://www.math.inc/position ; https://www.math.inc/release ; https://www.math.inc/sphere-packing |
| Licence of the source | None stated on the pages |
| Files in this folder | `source.pdf` (the position piece, printed), `note.md` |
| What was read | All three posts in full, with the 29 notes of the position piece. No repository was opened. The linked Lean model of WireGuard was not opened |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted. Every [P] here is a company
blog post. Surveys A, B and E already describe Gauss, the strong prime number theorem and the
sphere-packing run; this note does not repeat them.

## 1. What the work is

Gauss is Math Inc's agent for autoformalisation. Autoformalisation is the translation of informal
mathematics into a formal language such as Lean. In 2026 Math Inc published no description of how
Gauss works. Its newest text is a position piece on software verification. The piece argues that
verification at scale needs layers of mathematical models between the program and the property.
It argues against proofs written directly over machine code [P, position, Sections 1 and 2]. It reports two milestones on the WireGuard handshake in the Linux kernel. The sphere-packing
post gives Math Inc's own figures for the size of its Lean runs.

## 2. How it works

The position piece gives a method for one project, the verification of about 1.2K lines of C
[P, position, Section 3].

1. **Choose a shared semantic model.** A semantic model is a mathematical definition of what a
   program in a language does. Math Inc uses Cerberus, a model of C, through its Lean port. Cerberus
   translates C into a small language named Core [P, position, Section 3].
2. **Cut the code at service boundaries.** The handshake calls kernel services: time, networking,
   concurrency, allocators. Math Inc defines these boundaries and replaces the services by mock
   inputs [P, position, Section 3 and note 24].
3. **Run the model before proving.** The model executes a handshake inside Lean and is compared
   with a reference implementation [P, release]. This step found one case of undefined behaviour,
   and almost 40 gaps or performance faults in Cerberus or its Lean port [P, position,
   Section 3].
4. **Link the layers by a refinement theorem.** A refinement theorem states that a detailed model
   behaves as a more abstract model permits. Math Inc wrote an abstract semantics of Core and
   proved that the Cerberus interpreter refines it [P, position, Section 3].

The piece does not say which of these steps Gauss did.

## 3. How it splits a proof

The posts do not describe how Gauss splits a mathematical proof. They describe two splits of a
verification task.

- **Split by layer.** The unit is an abstraction layer: C source, Core, an abstract semantics of
  Core, and later the binary. A person chooses the layers. The check of the split is the
  refinement theorem between two layers, and a test run before any proof.
- **Split by boundary.** The unit is a component behind a service boundary. A mock stands for the
  other side. The piece calls this "tunnel to the middle" and says that it permits parallel work
  on a large stack [P, position, Section 3 and note 27].
- **The argument against.** The piece quotes Lamport (1997): "hierarchical decomposition does not
  simplify the total proof". It answers with Lamport's own condition: a decomposition is worth its
  cost "when the computer does a lot of it for you" [P, position, Sections 1 and 2].
- **The cost of no split.** Without source structure, agents "spend more tokens repeating
  themselves, or recovering any abstractions from the bottom up" [P, position, Section 2]. The
  piece cites a Google DeepMind report in which "a substantial fraction of our proofs concerns
  registers, stack frames and memory layout" [S, position, note 17].

For the dimension-8 sphere-packing run, the split came from the human blueprint. Gauss proved the
results that remained open in an existing project [P, sphere-packing, Section 2]. For dimension 24
the only input was the original paper [P, sphere-packing, Section 2]. No split is described.

## 4. What it says about scale

| Run | Lines of Lean | Time | Place |
|---|---|---|---|
| de Bruijn, June 2025 | 3,500 | not given | sphere-packing, Section 3 |
| Strong prime number theorem, September 2025 | 25,000 | not given in this post | sphere-packing, Section 3 |
| Sphere packing, dimension 8, remaining results | not given alone | 5 days | sphere-packing, Section 2 |
| Sphere packing, dimension 24 | not given alone | two weeks | sphere-packing, Section 2 |
| Sphere packing, total | from 70k to about 200,000 | three weeks | sphere-packing, Sections 2 and 3 |
| The same, before clean-up | 500,000 at peak | | sphere-packing, Section 4 |

Gauss refactored its own output from 500,000 lines to about 200,000 [P, sphere-packing,
Section 4]. The ratio is 2.5 (reader's computation). The post states that a proof that compiles
is not the end of the work. It names the harder task: to organise, integrate and maintain formal
knowledge [P, sphere-packing, Section 4]. No post gives agents, cost, tokens, build time or merge
conflicts for 2026. For software, the only size is 1.2K lines of C. No size is given for the Core
code that they expand to [P, position, Section 3].

## 5. Evidence

The evidence is three blog posts and a public Lean repository for sphere packing. There is no
benchmark, no baseline and no ablation. The position piece is an argument with two milestones. It
does not measure its claim that models and layers need fewer tokens [P, position, Section 2].
The WireGuard correctness proof does not exist yet. The release names it as work in progress
[P, release, Section 2]. Survey E records that Lean maintainers found the clean-up of the
dimension-24 code more trouble than it was worth [S, survey E, Section 1.5, from a blog by
Buzzard]. Math Inc's posts do not mention this.

## 6. Limits

Stated by Math Inc [P, position, Sections 2 and 3]:

- A semantics cannot be verified. It can only be validated.
- A source-level semantics is more permissive than a binary, so it needs "more general
  reasoning".
- Four questions stay open. One is how to extend C source proofs to binaries.

Found by the reader: Gauss, its models and its harness are closed. The role of Gauss in the
WireGuard milestones is not stated. The pages have no dates. The piece argues against a named
approach (a demonstration by the company Basis), so it is advocacy.

## 7. Relation to the two anchors

Both anchors are later than the sphere-packing post. Neither cites Math Inc (checked in the two
reference files). The date of the position piece is not known.

**Turing Agent (arXiv 2611.21299).** Turing Agent splits one statement into child statements and
checks that the children give the parent. Math Inc splits one verification into layers and checks
each pair of layers by a refinement theorem. The check has the same form: the lower level implies
the upper level. The difference is who chooses. In Turing Agent a model chooses each split. In
the position piece people choose the layers, and the layers are shared models that a community
agrees on.

**MathEye (arXiv 2611.22103).** MathEye asks a person to confirm an open claim. Math Inc's step 3
tests a model by execution before any proof. The two steps have the same purpose: find a wrong
statement at low cost. MathEye has no execution step.

## 8. What this repository can use

- **A move "layer by refinement".** The library's moves `interface-lemma` and `per-callee-lemma`
  cover a boundary inside one proof. A split into abstraction layers with a refinement theorem
  between them is wider, and it is not among the 17 moves. Survey D describes refinement in seL4
  and CompCert, so sources for entries exist.
- **Test a split before proving it.** Where a child statement is executable, run it on examples
  first. Math Inc found one undefined behaviour and almost 40 tool faults this way.
- **A clean-up factor as a cost measure.** 500,000 lines became 200,000. An experiment on
  decomposition can report lines before and after a refactoring pass, because the first count
  overstates the result.
- **Mocks at boundaries permit parallel work.** This is one answer to the interference problem:
  agents on two sides of a fixed interface do not edit the same files.

## 9. Open points and things not read

- How Gauss splits a mathematical proof, and how many agents it runs in 2026, is not public.
- The Lean model of WireGuard, the Cerberus Lean port and the sphere-packing repository were not
  opened for this note.
- The post "Introducing Gauss" (2025) is in the earlier surveys and was not read again.
- The date of the position piece must be confirmed.
