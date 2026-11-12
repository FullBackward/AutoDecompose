# D. Large verification projects: what their experience says about decomposition, interfaces, cost and scale

Prepared 2026-11-11 for AutoDecompose (rule-based decomposition of hard Isabelle/HOL problems into
short lemmas closed by bounded student agents; measured by tokens per closed leaf and by
decomposition correctness). Surveys A-C cover competition-scale proving only; this one covers
software and hardware verification projects, where decomposition, interface stability, parallel
work and maintenance cost have been lived with for years. It does not repeat A-C; pointers to them
are given as [A §x], [B §x], [C §x].

Method. Primary sources read directly: the seL4 papers as PDFs downloaded from trustworthy.systems
and sigops.org and converted locally with `pdftotext` (SOSP 2009, TOCS 2014, Cock et al. 2008,
Andronick et al. 2012, Bourke et al. 2012, Klein 2014 x2, Staples et al. 2014, Matichuk et al. 2015,
Greenaway et al. 2014); the l4v documentation and `crunch` source on GitHub; a shallow clone of the
public l4v repository (commit `1abfe5b`, 2026-11-10), counted with `grep`/`awk` only (nothing was
built or run); the local read-only AutoCorrode clone (HEAD `2026-06-15`), its `git log`, design
documents, prompts and theories; arXiv HTML for the 2024-26 AI papers; the PDFs of CompCert (CACM
2009), CakeML (JFP 2019), IronFleet (SOSP 2015), Cedar (FSE 2024), CertiKOS (CACM 2019), Project
Everest (TOPLAS 2026) and the Nitro Isolation Engine (ITP 2026 abstract, AWS whitepaper). Tags:

- **[P]** read in the primary source during this survey; "[P, measured]" means I counted it myself
  in the primary artefact (method stated);
- **[S]** secondary source only (search summary, another paper's citation) -- provisional;
- **[U]** unverified: recalled, or the source could not be opened.

Arithmetic of my own (ratios, means) is marked "my arithmetic". British spelling throughout.

---

## 1. seL4 / l4v (Isabelle/HOL, NICTA -> Data61 -> Proofcraft/seL4 Foundation)

### 1.1 The artefact in numbers

| Quantity | Value | Source |
|---|---|---|
| Kernel | 8,700 lines C + 600 lines assembly | SOSP 2009 §1 [P] |
| Abstract spec | 4,900 Isabelle LOC, 75 invariants | SOSP 2009 Table 1 [P] |
| Executable spec | 5,700 Haskell LOC -> 13,000 Isabelle LOC, 80 invariants | SOSP 2009 Table 1 [P] |
| C semantics | 15,000 Isabelle LOC, 0 invariants | SOSP 2009 Table 1 [P] |
| Refinement 1 (abstract <- executable) | 110,000 lines of proof | SOSP 2009 Table 1 [P] |
| Refinement 2 (executable <- C) | 55,000 lines of proof | SOSP 2009 Table 1 [P] |
| Whole first proof incl. frameworks, libraries, generated proofs | 200,000 lines | SOSP 2009 §5.2 [P] |
| Invariants | "over 150", "most are interrelated, many are complex" | SOSP 2009 §4 [P] |
| By 2012 | ~390,000 lines, 22,000 human-stated lemmas in ~500 theories; **95,000 lemmas including tool-generated ones**; full check 8 h | Bourke et al. CICM 2012 §1-2.1 [P] |
| By 2014 | 480,000 lines of proofs and specs ("~400,000 lines of proof script" in Klein FM 2014) | TOCS 2014 §1; Klein FM 2014 [P] |
| Today (l4v `proof/`) | 858 theory files, 860,349 lines, across five architectures; `spec/` 42,414; `lib/` 90,535; `tools/` 88,680 | [P, measured: `find -name '*.thy' \| xargs cat \| wc -l`] |
| Single-architecture view (generic + ARM of AInvs, Refine, CRefine) | 243,094 lines, 13,120 lemma/theorem statements, 1,618 `crunch` commands | [P, measured] |
| History | ~6,400 commits, 73 GitHub contributors, 68 named in CONTRIBUTORS.md | GitHub API, CONTRIBUTORS.md [P, measured] |

The CRefine (C refinement) proof is 59-75 k lines *per architecture* because it "is not split and
has a full copy per architecture"; AInvs, Refine, Access and InfoFlow have been split into generic
and `Arch` parts with a locale-based scheme (l4v `docs/arch-split.md`) [P].
https://github.com/seL4/l4v/blob/master/docs/arch-split.md

Effort (TOCS 2014 Fig. 19 [P]; starred numbers there come from week-by-week effort records):
kernel development 2.2 py (Haskell prototype 2 py, C 2 pm); correctness proof 20.5 py, of which
generic frameworks and tools 9 py, abstract spec 4 pm, executable spec 3 pm, refinement 1 8 py,
refinement 2 3 py; fastpath 5 pm (one engineer part-time over 7 months); integrity 7.4 pm (10,500
lines); confidentiality 40.7 pm (1.8 pm scheduler change, 18.5 pm making the abstract spec
deterministic and repairing the correctness proofs, 20.4 pm the proofs themselves); binary
verification ~2 py (two people over 20 months); capDL 2 py (spec 7.2 pm, three contributors;
refinement 17.2 pm, four to five people, one contributing 9.7 pm). Cost: $362/SLOC for 22.7 py
(TOCS §7.2.3) [P]. Klein's FM 2014 abstract gives "12 person years ... for the proof itself, and
another 12-13 person years for developing tools, libraries, and frameworks" [P]; the two accounts
differ by 1-4 py in the tool share, and I use the TOCS table. Team: "on average 12 people over 4
years (about 7 full-time equivalent)" (Klein, "Proof engineering challenges for large-scale
verification", 2014) [P]. https://trustworthy.systems/publications/nicta_full_text/7371.pdf

Proof-to-code ratio, my arithmetic from the SOSP table: 165,000 lines of refinement proof for 8,700
lines of C is about 19:1; 200,000 total is about 23:1.

### 1.2 How the proof is decomposed

**Layers.** Abstract spec <- executable spec (generated from the Haskell prototype) <- C semantics
(generated by the C parser) <- binary (translation validation), each linked by forward-simulation
refinement, composed by transitivity (TOCS §4, Theorems 1-3) [P].

**Unit of work: one function, two kinds of lemma.** "The proof in our refinement and Hoare logic
framework decomposes along function boundaries. Each unit of proof has a set of preconditions ...,
a statement or sequence of statements in a function that modify the system state, and the
post-conditions that must hold afterwards" (SOSP §3) [P]. For each kernel function there is one
*correspondence* (`corres`) lemma per refinement step and "one or many" *invariant* (Hoare-triple)
lemmas; "Many abstract functions come with dozens of different invariant lemmas"; non-failure is kept
in the single correspondence proof; "we have aimed to move effort from the correspondence proofs to
the invariant proofs, which, with code from only one specification level present, are technically
more straightforward"; nonetheless "the invariant proofs are typically the hardest component"
(TOCS §4.5) [P]. In refinement 1, **80 % of effort went into invariants and 20 % into
correspondence**; the C refinement proved *no* invariants on C at all (SOSP §5.2) [P].

**The `corres` calculus is itself a decomposition rule.** `corres` "decomposes over the bind
constructor through the corres-split rule"; proofs "take a common form": unfold, weaken the
precondition to a schematic, split with the splitting rules, close the component `corres` goals with
existing results, let the VCG discharge the Hoare triples, and finally prove the original
precondition implies the one actually used (Cock, Klein, Sewell, TPHOLs 2008 §5) [P].
https://trustworthy.systems/publications/nicta_full_text/483.pdf

**`wp` is a syntax-directed VCG.** Weakest-precondition rules for each monadic primitive, applied
repeatedly; non-weakest rules are allowed ("we do not affect the soundness of the VCG, we simply take
the risk that the implication ... is not provable"); postcondition conjunctions handled by lifting
rules (Cock 2008 §4) [P]. In today's l4v the `wp` family appears 13,990 times and `wpsimp` 7,793
times in `proof/` [P, measured: `grep -o '\((wp|wp_once|wpc|wpfix)\b'`, `grep -o '\bwpsimp\b'`].

**`crunch` generates lemma statements from the call graph.** Its header comment: given a property
`P ⊢ f` for a top-level function `f` "defined in terms of subfunctions g etc.", crunch "will first
show many lemmas P ⊢ g"; it finds a "crunch rule" (typically from the definition), then
"recursively appl[ies] to almost all monadic constants in all of the premises", reuses an existing
rule if crunch already proved one, a `wp` rule solves it, or a lemma with the name crunch would use
already exists, and stops at a user-maintained `crunch_ignore` set; the leaves are closed by `wp`
and `simp` (l4v `lib/crunch-cmd.ML`) [P].
https://github.com/seL4/l4v/blob/master/lib/crunch-cmd.ML . In the single-architecture view there
are 1,618 `crunch` commands naming 2,136 target functions (mean 1.32 per command), each expanding
recursively over its callees, so 2,136 is a lower bound on the lemmas generated [P, measured, awk
over the text between `crunch` and `for`]. The idea is already in Cock 2008: "Simple invariants can
often be stated and proved automatically for many functions at a time" [P].

**Lifting lemmas** handle the cases crunch cannot: invariants that discuss only part of the kernel
heap, preserved by functions that touch a different part (l4v `docs/de-duplicating-proofs.md`) [P].

### 1.3 Mechanical versus human-designed

| Generated by tools from program structure | Designed by people |
|---|---|
| Executable spec (Haskell -> Isabelle translator, 3 pm to set up) [P SOSP] | Abstract spec (4 pm) [P] |
| C semantics (C parser); bitfield code *and* its proofs (Cock 2008 bitfield generator) [P TOCS] | The 150+ invariants, especially the "algorithmic invariants ... where most of the proof effort was spent" (SOSP §4) [P] |
| AutoCorres abstractions with proofs: spec 25-53 % fewer lines, terms 40-61 % smaller than C-parser output (PLDI 2014 §5.1) [P] | Correspondence statements and return-value relations chosen in `corres-split` [P Cock] |
| `crunch` lemmas over the call graph [P] | Lifting lemmas, loop/recursion arguments, the choice of preconditions [P] |
| `wp` verification conditions, one per program step [P] | Where to cut layers (e.g. making the abstract spec deterministic, 18.5 pm) [P TOCS] |

The single most useful number for this project: in 2012, **22,000 human-stated lemmas, 95,000 with
tool-generated ones** (Bourke 2012 §2.1) [P]: about three quarters of the lemma statements in the
largest Isabelle verification were produced by rules from structure, not written by people (my
arithmetic). Word arithmetic alone took "approximately 25 % of the 30 000 lines of proof library"
(Greenaway et al. PLDI 2014 §3.1) [P], which is what AutoCorres's word abstraction removes.

### 1.4 Typical lemma size

- Matichuk et al. (ICSE 2015) measured AInvs: 2,790 lemmas, top-level proof size 32,214 lines;
  Refine: 4,143 lemmas, 67,856 lines; Access: 724 lemmas, 8,116 lines; InfoFlow: 1,665 lemmas
  (§V-A) [P]. Since a top-level proof size counts every lemma in its dependency cone, these give a
  mean of about 11.5, 16.4 and 11.2 lines of proof per lemma (my arithmetic).
  https://trustworthy.systems/publications/nicta_full_text/8318.pdf
- FVELer (seL4 lemmas extracted with PISA): 29,125 lemmas, 200,646 proof steps; mean 6.9 steps;
  **12,089 lemmas (41.5 %) are one step, 25,046 (86 %) at most ten steps**, 28,954 within 100; max
  963 (arXiv 2406.14408v2 §4.5, Table 1, Fig. 4) [P]. https://arxiv.org/html/2406.14408v2
- My count over the single-architecture view: 13,093 top-level lemmas, lines from statement to the
  next top-level command (statement, proof and trailing blanks): mean 15.6, median 8, p75 14, p90
  28, p99 139, max 1,012 [P, measured, awk]. The distribution is very skewed: a few hundred long
  `ccorres` proofs, a large mass of one-to-ten-line `wp`/`clarsimp` lemmas.

### 1.5 Statement size predicts proof size, quadratically

Matichuk et al. analysed 15,018 lemmas, ~215,000 lines (four seL4 developments and two AFP
entries). Statement size = number of unique definitions reached recursively from the statement.
Result: "a consistent quadratic relationship between the size of the formal statement of a property,
and the final size of its formal proof", R² 0.154-0.845 on the raw measure; with an *idealised*
measure that drops constants whose definitions the proof never unfolds, R² 0.73-0.937 (Abstract,
§VI) [P]. The low raw fits were caused by **over-specified statements**: lemmas mentioning the whole
abstract specification while stating a general property. Linear and exponential fits were worse;
cubic added nothing. This confirmed the project leader's earlier rule of thumb that "for microkernel
refinement proofs, proof size scales roughly quadratically with code size", explained by every
invariant having to be preserved by every feature (§I) [P]. Cock 2008 had already hypothesised that
the whole verification "was quadratic in the size of the kernel" while "the refinement proof itself
remains linear" (§6.4) [P]. Caveat from the authors: the relation is explanatory, "not yet
necessarily predictive", and phases (definitions, statements, proofs) iterate in practice.

Staples et al. (ESEM 2014) closed the other half: across nine seL4 projects, **Total effort
(person-weeks) = 9.98 + 3.35 x final size (kLOP)**, R² = 0.914; across 24 individual contributions,
R² = 0.93; team size, schedule pressure and difficulty had no significant effect at 0.05; years of
experience had none (§4, Table 1) [P]. Table 1 gives final size, effort and maximum team size per
project, e.g. Exec-to-Abstract refinement 96.6 kLOP, 368 pw, team 6; Code-to-Exec 53.3 kLOP, 138 pw,
team 6; Info flow 27.1 kLOP, 75.9 pw, team 8; Integrity 7.05 kLOP, 28.5 pw, team 4 [P].
https://trustworthy.systems/publications/nicta_full_text/8105.pdf

### 1.6 People, partitioning, interfaces

- Who partitioned: the verification team designed "refinement calculi for each of the major proof
  steps that allowed the work to be divided up among members of the team. Especially in the
  code-level proof, individual lemmas proving the correctness of separate functions in the kernel
  implementation could be proved independently. In the design-level proof, the same could be
  achieved once the formulation of invariants had stabilized" (Andronick et al. ICSE 2012 §IV-C)
  [P]. https://trustworthy.systems/publications/nicta_full_text/5396.pdf
- How far it scaled: "Up to four people worked on this proof concurrently and independently without
  much conflict. We estimate that for code of this size (10K lines of C code) a team with more than
  five or six persons would need a more serious effort in planning and synchronisation" (Cock 2008
  §6.4) [P]. Later, up to six people worked on one module (Bourke 2012 §2.4, Fig. 4) [P].
- Interfaces were not small or stable. Ideal: "a compositional calculus that allows clean, small
  interfaces between sub-tasks, which are defined once and remain stable. In reality, this is rarely
  the case." What worked was "compositionality under side-conditions": people worked on the same
  property for different parts, or different properties of the same part; when side-conditions
  changed, communicating them was overhead, "inevitable when for instance an invariant is discovered
  incrementally by the entire team. The faster the discovery, the smaller the overhead." Remedy for
  drift: "state the final top-level theorem first, and ... use a continuous regression test to check
  that the parts still fit", to avoid discovering late "that an overly weak statement in one
  sub-proof requires significant rework in another" (Bourke 2012 §2.4) [P].
  https://trustworthy.systems/publications/nicta_full_text/5717.pdf
- Ordering: design-level and code-level verification "could run in parallel. However, significant
  savings in code-level verification were possible because the invariants from S4 had stabilized.
  Starting S6 too early may negate this effect"; design verification (S4) took 60-70 % of effort
  (Andronick 2012 §III-A) [P].
- Invariant discovery: starting from the minimal invariant and growing it on demand was a mistake:
  "At multiple points we hoped to get away with a simpler formulation, but then were caught out
  halfway through the kernel by a particular operation after several thousand lines of proof ... in
  such a complex system, the simple formulation is unlikely to succeed. Take the precise formulation
  instead"; "a good source of invariants is the development team" (Cock 2008 §6.4) [P].

### 1.7 Cost of change and maintenance

SOSP §5.3 and TOCS §7.2.4 [P]: local optimisations cost re-verification "roughly proportional to the
size of the change" (1 day to implement, 2-3 days to verify; in one case invariant knowledge shrank
a 20-line patch to one line); a new system call batching existing ones: 1 day to implement, <1
person-week of proof; interrupts, ARM page tables and address spaces: 12 % of Haskell modified, 37 %
added, 1.5-2 py, about **32 % of the original verification time**; reply capabilities: <5 % of the
code, ~1 py, **17 % of the original proof effort**, because they "fundamentally broke a number of
properties and invariants on capabilities" and some new preconditions "turned out not to be true".
Andronick 2012 §III-B, §IV-D [P]: maintenance ran at about one full-time person with one to three people
updating proofs on demand; significant features took ~6 months of re-verification; for local
changes the proof cost is "often a factor of roughly 3-5" of the code change (e.g. 2 h to implement,
6 h to re-verify). The proof became a regression suite run after each commit that "identifies which
specific portions of the proof must be re-established" (TOCS §7.2.1) [P]. L4.verified also had a
proof cache: a theorem is skipped if none of its statement's dependencies changed, though "even just
scanning definitions and lemma statements without proof can still take tens of minutes" (Bourke
2012 §2.2) [P].

### 1.8 What broke at scale

From Bourke 2012 and the l4v docs [P]: no one person understands the whole proof (Klein's
definition of "large scale"); finding the right existing lemma among tens of thousands (they built
`find_theorems` for this); placing a general lemma (a lemma-moving tool, Levity); naming ("it can
take longer to think about a lemma's name than it takes to prove it"); conventions decay within
months without mechanical policing; edit-check cycles of hours after a change far upstream;
duplication ("17 suspiciously similar helper lemmas", `de-duplicating-proofs.md`); copy-per-
architecture for CRefine; Isabelle upgrades roughly yearly; brittle `vcg` schematic instantiation to
`False` (`vcg-debugging.md`); the advice to *compact* exploratory `apply` scripts into single
`fastforce` calls, with the warning that compacted proofs "may be harder to fix once they do break"
(`compacting-proofs.md`). Klein's own list of AI opportunities (2014): analogies within large case
splits, recurring fragments across engineers, automatic lemma extraction, and "automatically
generalising and re-proving lemmas whose statement was needlessly specific" [P].

### 1.9 LLMs on seL4

| Work | Unit and set | Model, budget | Result | Tag |
|---|---|---|---|---|
| Selene (Zhang, Lu, Duan; arXiv 2401.07663, 2024) | seL4 lemmas with dependencies | GPT-3.5/4 | 27.06 % best average on 340 sampled theorems (as cited by AutoReal); "nearly 40 %" of its items need one-line proofs (as cited by the OSDI paper) | [P abstract; S numbers] |
| FVEL / FVELer (NeurIPS 2024 D&B; arXiv 2406.14408) | 29,125 seL4 lemmas; test 1,077, test-hard 852 | Llama-3-8B, Mistral-7B, LoRA | Fine-tuned 74-88/1,077 on test, 49-64/852 on test-hard (Table 6) | [P] |
| AutoReal (Zhang et al., arXiv 2602.08384, Feb 2026) | 660 theorems: one whole theory per l4v proof category; context **supplied by hand** ("not yet automated") | Qwen2.5-Coder-7B fine-tuned on ~200k step rationales; up to 256 whole-proof attempts | 341/660 = 51.67 % (5 attempts: 37.1 %); crefine 28.26 %, refine 47.27 %, invariant-abstract 54.29 %; ablation on 105 theorems: base 0.95 %, +CoT 22.86 %, +context 5.71 %, both 54.29 % | [P] |
| Neuro-symbolic proof search (He et al., OSDI'26; arXiv 2603.19715) | FVELer val/test/test-hard | Mistral-7B or Qwen3-1.7B fully fine-tuned on 181,887 state-step pairs; best-first search, 5 states x 128 candidates per iteration; Sledgehammer 60 s on top 16 states when search stalls; 120 min per theorem | 77.6 % total (Mistral) vs **Sledgehammer alone 40.3 %**, FVEL 7.8 %, Selene 5.6 %, `auto` 5.9 %; **by proof lines only 36.2 % of the corpus** (Sledgehammer 15.0 %); 692 unsolved; 60.1 % of step errors are "undefined fact"; 23 of 241 validation failures had genuine counterexamples traced to **assumptions dropped when the benchmark sliced the scripts**; mean time to success 139 min; ~$4.1/theorem with API models (DeepSeek v3.2: 5.5 % plain, 33.0 % with RAG and search, 52.0 % adding the hammer) | [P] [A §1.12] |
| CAPRI (Woodcock et al., arXiv 2608.13459, Aug 2026; not seL4) | 12 failed proofs from four Isabelle developments, 180 runs | unnamed API models | iterative 32/36 vs one-shot 22/36; **6 of 144 Isabelle-accepted candidates had edited protected text**, all from workflows that could edit a whole theory; a proof-body-only interface removed them at 29/36 vs 31/36 | [P abstract] |
| seL4 Summit 2026 programme | -- | -- | six abstracts mention AI; none reports proof automation results on l4v | [P] |

Readings. (i) Success by theorem count overstates: 77.6 % of theorems is 36.2 % of proof lines, so
the solved set is the short tail. (ii) A general hammer alone already closes 40 % of seL4 lemmas at
a 2 h budget, consistent with FVELer's 41.5 % one-step lemmas. (iii) The hardest area for every
system is CRefine (`ccorres`), the layer with the heaviest custom machinery. (iv) Slicing a lemma
out of its development without its full context manufactures false statements. No published work
applies an LLM agent to l4v maintenance (proof repair across kernel versions); I found none.

---

## 2. AutoCorrode (Isabelle/HOL, AWS Automated Reasoning Group)

### 2.1 What it is and how big

AutoCorrode is "infrastructure for reasoning about imperative programs in Isabelle/HOL", classical
and separation logic, with "configurable and scalable custom automation, written in Standard ML";
language-agnostic core, frontend for µRust; named as the "little rusty brother" of AutoCorres
(README) [P]. Authors per README/AUTHORS: Becker, Chong, Dockins, Grundy, Hu, Mulder, Mulligan, Mure,
Paulson, Slind [P]. Local clone [P, measured]: 487 commits from an import on 2025-03-30 (earlier
history squashed) to 2026-06-15; committers Mulligan 232, Becker 210, Mulder 54, Paulson 5, others
1-2; 373 `.thy` files, 56,830 lines; 20 `.ML` files, 8,732 lines; 2,731 lemma/theorem statements;
Crush 7,991 lines (`.thy` + `.ML`); plus 44,549 lines of Scala and 17,807 of Python tooling. Activity
peaked at 248 commits in February 2026, overwhelmingly in the `isabelle-assistant` tooling (862 file
touches in Feb-Mar 2026). An experimental C11 frontend (used on mlkem-native `poly.c`) was removed to
a fork on 2026-03-25 [P, git log].

Its production use: the **Nitro Isolation Engine**, a Rust hypervisor component on Graviton5,
verified in Isabelle/HOL with "approximately 330,000 lines of machine-checked models and proofs"
covering functional correctness (with memory safety, termination, absence of runtime errors),
noninterference-style confidentiality and integrity, over core VM-management hypercalls, power
management and part of abort handling, with PCI and virtual GIC still to come (Becker et al., ITP
2026 invited talk, LIPIcs.ITP.2026.1) [P]. The AWS whitepaper names the toolchain: µRust model of
each hypercall, separation-logic contracts, a weakest-precondition calculus with "extensive custom
proof automation", a two-level specification (declarative state-transition spec refined by the
separation-logic functional spec), and conformance testing against the binary [P].
https://drops.dagstuhl.de/storage/00lipics/lipics-vol382-itp2026/LIPIcs.ITP.2026.1/LIPIcs.ITP.2026.1.pdf ;
https://d1.awsstatic.com/onedam/marketing-channels/website/aws/en_US/whitepapers/compliance/nitro-isolation-engine-whitepaper.pdf .
No person-year figures are published; no research paper on AutoCorrode itself was found
(searched for the project and author names) [searched].

### 2.2 How a verification goal is decomposed

From `Micro_Rust_Examples/Showcase.thy` and the whitepaper [P]:

1. **One contract per function** (`make_function_contract pre post`, separation-logic pre/post).
   In the Nitro work each hypercall's behaviour is given by a **Machine Readable Specification (MRS)
   from which both the Rust code and the Isabelle definitions are generated**, "a single source of
   truth for both the engineering and verification teams" (whitepaper, "Built from the start for
   verification") [P]. Statements are therefore stabilised by generation, not by negotiation.
2. `crush_boot f: <def> contract: <contract_def>` unfolds function and contract and turns
   `Γ; f ⊨F contract` into a weakest-precondition entailment.
3. `crush_base` symbolically executes the body and discharges what it can.
4. The human supplies what automation cannot: loop invariants (`INV=...` in the for-loop rule, which
   leaves two subgoals: invariant established/postcondition implied, and body preserves invariant),
   helper facts, and occasionally a `goal_cases` split.
5. Callees are handled either **modularly** (`specs add: callee_spec contracts add: callee_contract`,
   i.e. use the callee's proved contract as a lemma) or by **inlining** (`inline: callee_def`) and
   re-executing. Both are shown on the same example.

Other structural rules visible in the code [P]: theories split into `Foo.thy` (definitions) and
`Foo_Lemmas.thy` "where the proof burden is large"; **separation lenses** let a proof done over a
small separation algebra be "pulled back" to a larger one, so per-component proofs compose without
boilerplate; references are typed through *foci* so the same proofs hold for an abstract heap and a
byte-level memory. The whitepaper adds design-for-verification constraints in the code: a minimal
code base, and hypercalls written around a transaction primitive with strict two-phase locking so
that concurrent behaviour serialises [P].

### 2.3 Crush

From `Crush_Examples.thy` [P]: crush "is never trying to be 'clever'. Its goal, instead, is to do the
(seemingly) obvious thing reliably, and to discharge hundreds or thousands of elementary reasoning
steps without human intervention", leaving the author "the tasks of calling crush suitably ... and
filling in the steps that crush cannot solve (such as providing loop invariants)". Structurally it
is "a long disjunction of different branches", ordered for correctness (introducing schematic
variables must come after introducing free variables) and for performance (`simp`/`clarsimp` at low
priority; `force`, `blast`, `auto` "not considered at all"). "Complex proofs require hundreds of
iterations of the crush loop." Configuration is essential: "a bare `apply crush` is rarely getting
far". Variants: `crush_base` (all goals), `fastcrush_base` (current goal and its descendants, "more
robust"), `crush_base_step` (one iteration, debugging). Tooling: per-branch timing profiles
(`apply\<tau>`, `show_timelogs`), logging of which branch instantiated a schematic (because "a
branch silently picking the wrong instantiation" is "a common source of failures deep inside a
crush run"), and an adaptation of the Meng-Paulson relevance filter to *premises* (`mepo_prem.ML`)
to keep `simp` fast on goals with very many hypotheses. The git log shows Crush being tuned through
2026 (eager substitution, duplicate-premise removal, prioritising premises that determine
schematics, hoisting per-step setup) [P].

### 2.4 Agent tooling

- **I/Q** (jEdit plugin, MCP over localhost TCP): 19 document tools (`read_file`, `write_file`,
  `get_context_info` with goal state, `get_proof_blocks`, `get_diagnostics` with a theory-scoped
  `file_summary`, `get_sorry_positions`, `explore` with `query = proof | sledgehammer |
  find_theorems` run "non-invasively" in an overlay, ...) plus 20 `repl_*` tools; token
  authentication and read/mutation root restrictions; "I/Q is mechanism _only_: It needs to be
  complemented with behavioral guidance" (`iq/README.md`) [P].
- **I/R** (REPL outside jEdit): REPLs are lists of Isar steps that can be forked at any step, edited
  (later steps marked stale), replayed, truncated or merged back into their parent; rooted in
  theories or, with `record_theories` heaps (~5x larger), at arbitrary points inside a theory
  (`ir/README.md`) [P]. Commits record why: concurrent MCP clients so "an agent ... can spawn multiple
  subagents working concurrently in separate REPLs"; timing data because "without timing data from
  REPL steps, agents have a hard time optimizing proofs for performance" (2026-03-29) [P].
- **I/C** (file checker on I/R): incremental rebuild by content hash, "within a changed file,
  unchanged command prefixes are preserved -- only the changed tail is re-stepped"; on failure,
  dependents are marked stale, not checked; parallel `-j N` (`ic/README.md`) [P].
- **Isabelle Assistant** (Bedrock): about 50 tools in the README (35 in the Feb 2026 design doc);
  generated proofs verified through I/Q and retried with errors; defaults `max_tool_iterations` 10,
  `verify_timeout` 30 s, `sledgehammer_timeout` 15 s, `nitpick`/`quickcheck` 5 s,
  `max_context_tokens` 60,000 with auto-summarisation at 75 %; a `plan_approach` tool that
  brainstorms three approaches, elaborates each in a parallel read-only sub-agent (24 tools), then
  selects one, after which the main agent turns the plan into `task_list` items; persistent topic
  memory (README; commit `1d2942d`) [P]. A layering gate makes Isabelle execution IQ-only (design
  docs 01-02, 09) [P].

### 2.5 Rules given to agents for writing Isabelle

`iq/iq_guidance.md` [P], verbatim in part: "ask yourself: Could my proofs be ... broken up into
smaller lemmas?"; for short proofs try `by ...` or apply-style, "Try 1-2 tactics at a time ... DO NOT
repeatedly replace entire proof scripts"; for long ones "work top-down: First, establish the rough
structure, using `sorry` to temporarily axiomatize core steps. Then, fill in those `sorry`s one at
a time; if they are complex, hoist them out as separate lemmas". Design document 05 ("Agent-Generated
Isabelle Proof Style Guide") and system prompts 00-04 [P]: never fabricate facts, names or states;
structured Isar over long `apply` chains; "Treat `auto`/`simp_all` as terminal clean-up steps";
avoid "brittle one-line `metis`/`smt` proofs when a short structured derivation is clearer"; inspect
state, retrieve facts, validate candidate steps with tools, edit, then check to end of file; "Use
`find_counterexample` to falsify conjectures before deep proof attempts"; "Do not loop on identical
failing tool calls". The `suggest_strategy` prompt makes the model pick *one* of six strategies
(induction, case analysis, contradiction, direct, rule application, coinduction) and name the first
command and key lemmas -- a small fixed menu of decomposition moves.

### 2.6 Lessons recorded in the history

- "models would call the same tool (set_cursor_position, edit_theory, etc.) 60+ times with identical
  arguments" -> stuck-loop detection, window 3, later 6 with A-B-A-B detection (commits `793abf1`,
  `ae27bef`, Feb 2026) [P].
- "Deep audit of all 29 LLM tools revealed critical bugs ... that caused the agent to get stuck in
  loops and produce corrupted output"; fix includes returning surrounding context after every edit
  "so the agent can verify success without a separate read" [P].
- `write_file` "frequently reported success while the file still had errors": the counts were
  range-scoped but read as theory-scoped, and "an upstream change that invalidated proofs further
  down produced no signal at all -- the agent saw commands_failed: 0 and moved on". Fix: separate
  `edit_summary` and `file_summary`, and a `check_context_scope` to re-check the rest of the proof
  before returning (commit `ed62a28`, June 2026) [P].

Provenance. `CLAUDE.md` and `MCP.md` in the local clone are **untracked files, not upstream**
(`git status`); I treated them as local notes and attribute nothing in them to AWS. No commit carries
an AI co-author or "generated with" trailer; whether any commit text or code was agent-written
cannot be determined from the history [U]. The repository does address "agent-generated
contributors" explicitly in its steering documents (00, 04, 05) [P].

### 2.7 Uses outside AWS

Kappelmann et al., "Just Type It in Isabelle!" (arXiv 2604.15713v3, 2026) drove Isabelle through
Isabelle/Q with Claude Opus 4.6 in OpenCode: formalisations of 1,938 and 2,071 lines for $139 and
$140; a generalisation of ~1,800 lines for $93; human review found **misaligned statements**
(completeness about the wrong set, a locale assumption that could be instantiated arbitrarily); the
agent "often skipped the prescribed gradual workflow and wrote large Isar proofs at once"; human
help with Isabelle itself was needed once (§6.2-6.4) [P]. Paulson's AITP slides (undated in the
text) report a HOL Light port that "blew up from 214 lines to nearly 1500 due to verbose and needless
calculations" and generally "needlessly fine-grained" Claude proofs, "1000s of lines often with
duplication/symmetries" [P]. https://aitpm.github.io/slides/Paulson.pdf

---

## 3. AI on large verification codebases beyond seL4

**VeruSAGE** (Yang, Neamtu, Hawblitzel, Lorch, Lu; arXiv 2512.18436v2) [P]. 849 tasks from eight
Verus-verified systems (Anvil, IronKV, a memory allocator, Node Replication, NRKernel, Atmosphere,
a storage system, Vest). **Unit: one non-trivial function's proof**; dependencies extracted into a
standalone file, **dependent proof bodies replaced by `unimplemented!()` and marked
`external_body`**, the target's pre/postconditions kept and its proof annotations removed; mean file
~947 lines (§3.1). Best per model: o4-mini 41 %, GPT-5 55 %, Sonnet 4 64 %, Sonnet 4.5 81 %;
hands-off cost $0.81-6.65 and 3.3-9.2 min per task; AutoVerus reaches 20 % on this set (Tables
4-7). Success correlates negatively with task size (-0.28 to -0.50); Sonnet 4.5 proofs have median
24 added lines against 9 for human proofs; Sonnet struggles when definitions are hidden behind closed
specs; without a cheat checker Sonnet 4 cheated on 14 % of tasks (§5.3-5.6). On unfinished human
proofs in Atmosphere, Sonnet 4.5 completed 23 of 25 functions (~$8.45, 13.5 min each) and **flagged
five lemma specifications for adjustment, all confirmed by experts** (§5.2).
https://arxiv.org/html/2512.18436v2

**Vero** (Ye et al., arXiv 2608.13522, Aug 2026) [P]. 43 multi-module Lean 4 repositories (from Dafny,
Verus, Coq and Python sources; 743 APIs, 2,705 specifications); 90-minute budget; best agent (GPT-5.5
xhigh) fully solves 27/43 (code-and-proof) and 25/43 (proof-only); about $15-67 per instance (my
arithmetic from Table 2). Findings (§4.2): "The bottleneck is not local proof skill";
"Completed repositories are organized around reusable lemma libraries rather than independent proofs
per specification": **helpers hold a median 73.6 % of proof lines**, and in 80 of 82 full solves a
helper is shared by at least two specifications; specs needing a prerequisite chain of depth four or
more pass at 50.6 % against 83.9 % with no helper; residual failures "form a cluster that shares a
few missing invariants, so closing them requires the inductive generalization the agent never found,
not additional proof attempts"; crossing module boundaries adds little, unfolding supplied
definitions and iterated behaviour adds a lot (+14.9 and +11.7 points of failure); agents fix the
implementation early and "treat [it] as fixed scaffolding rather than a lever".
https://arxiv.org/html/2608.13522

**Other Verus/Dafny/F\*/HOL Light work.**
- AutoVerus (OOPSLA 2025, arXiv 2409.13082): three agent phases (generate, refine with tips, debug
  with verifier errors); >90 % of 150 tasks, over half in <30 s or 3 LLM calls [P abstract].
  AlphaVerus (treefinement, LLaMA-3.1-70B) and SAFE (self-evolving fine-tuning, VerusBench 70-79 %
  depending on version) [S].
- RagVerus (arXiv 2502.05344): repository-level retrieval, 27 % relative gain on 383 tasks; RVBench
  755 tasks in a later version; KVerus (arXiv 2605.03822): 183/359 (51.0 %), concluding that
  repository-level proof needs cross-file context and lemma reuse, not repeated prompting [S].
- Vericoding benchmark (Bursuc, Tegmark et al., arXiv 2509.22908): 12,504 specifications; model-union
  success Dafny 82.2 %, Verus 44.2 %, Lean 26.8 %; natural-language descriptions did not help [S].
- F\* (Chakraborty et al.), as reported by the Everest retrospective: a 940,000-line dataset mostly
  from Everest; best model synthesised ~35 % of lemma proofs, 41 % of dependently typed definitions,
  61 % of simply typed goals (TOPLAS 2026 §5.3) [P via Everest].
- Laurel / DafnyGym (arXiv 2405.16792): helper assertions in real Dafny code (stdlib, Cedar,
  DafnyVMC); naive prompting struggles; placing a placeholder at the verifier's error location and
  retrieving structurally similar lemmas gave >50 % of required assertions [S].
- s2n-bignum-bench (Rao, Harrison et al., arXiv 2603.14628): 2,284 HOL Light obligations from AWS's
  verified assembly; zero-shot frontier models at most 6.35 % given only the goal term [S].
- Goedel-Code-Prover (arXiv 2603.19329, COLM 2026): Lean code verification; one 8B policy both
  decomposes goals "into structurally simpler subgoals" and proves them; a "decomposition score that
  combines constructive justification with structural effectiveness" is both RL reward and
  inference ranking; 62.0 % on 427 tasks; success "improve[s] monotonically with search iterations"
  while whole-proof baselines plateau [P abstract] [A §4.7].

---

## 4. Short entries

**CompCert** (Coq) [P, Leroy CACM 2009]. 42,000 lines of Coq, ~3 py; 14 % compiler algorithms, 10 %
semantics, 76 % proof; 14 passes through 8 intermediate languages; **each pass 1,500-3,000 lines of
spec and proof**, each IL 300-600 lines, plus 10,000 lines of shared infrastructure. Passes compose by
transitivity of semantic preservation, so the unit of work is a pass with a fixed source and target
semantics. Register allocation is **translation validation**: the George-Appel colouring heuristic is
unverified OCaml, checked a posteriori by a small verified validator, because colouring is "easier to
validate a posteriori than to directly prove correct". Lesson: when generating an object is hard to
prove correct, verify a checker of its output instead; and fix the interface (IL semantics) before
fanning out passes. https://xavierleroy.org/publi/compcert-CACM.pdf

**CakeML** (HOL4) [P, Tan et al. JFP 2019 §1-2]. Backend through 12 intermediate languages; design
rule D0: introduce a new IL "whenever a significant higher-level language feature has been compiled
away, or when a new lower-level one is introduced", because ILs that mix levels "complicate the
invariants needed to verify transformations". Bootstrapped in the logic. Lesson: choose the grain of
intermediate statements so that each invariant mentions one level of abstraction. (No effort figures
in the paper.)

**IronFleet** (Dafny) [P, Hawblitzel et al. SOSP 2015 §3, §6-7]. Layers: high-level spec (IronRSL 85
SLOC, IronKV 34), distributed protocol, implementation, linked by TLA-style refinement and
Floyd-Hoare reasoning. Totals: spec 1,400, implementation 5,114, proof 39,253 SLOC (about 7.7:1 proof
to code overall, my arithmetic; 3.6:1 at the implementation layer); ~3.7 person-years. Serial build
~6 h, but per-file verification is farmed out in parallel so developers "rarely [wait] more than 6-8
minutes"; IDE feedback in 1-10 s. Modularity is enforced by **`opaque`/`reveal` and per-scope fuel**
to keep the SMT search space small and avoid timeouts; invariants are preferably stated over the
monotone set of sent messages, which makes them easier to prove. Lessons: small trusted top
statements; hide definitions by default; keep the checker fast enough that a leaf check is seconds.
https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf

**Project Everest** (F\*, Low\*, Vale; MSR, Inria, CMU, 2016-) [P, Ahman et al. TOPLAS 2026]. About
1.3 million lines of non-generated F\*; a full build takes ~2 h on 24 threads, issuing ~66,000 SMT
queries for ~622,000 proof obligations; HACL\* is ~245,000 lines of F\*/Vale yielding ~135,000 lines
of verified C and assembly. The standard proof style is **two-step**: Low\* code against a low-level
functional spec, then that spec against a high-level spec, "enabling different people to work on the
two parts of the proof in parallel" and separating memory reasoning from functional intent (§3).
Metaprogrammed generic code gives many verified variants from one proof. Failure mode at scale:
**SMT proof instability** -- renaming a variable or changing solver version can flip a proof;
"Particularly painful is when a change one developer makes triggers an instability-related failure in
another developer's code"; mitigations: module abstraction and opacity, structured `calc` proofs,
small resource limits (large-limit proofs "have become notorious among the maintainers") (§4.3) [P].
https://mtzguido.github.io/pubs/everest.pdf

**CertiKOS** (Coq) [P, Gu et al. CACM 2019 §2, §5.1]. Certified abstraction layers (underlay
interface, module, overlay interface) composed horizontally, vertically and in parallel, so "an
otherwise prohibitive verification task can be decomposed into many simple and easily automatable
ones". mC2: 6,500 lines of C and assembly; sequential mCertiKOS ~2 py; concurrency framework ~1 py;
concurrency extensions ~2 py; 5,249 lines of added specs, ~40k lines of auxiliary definitions,
lemmas and invariants, 50k lines of proof for the concurrency features; sequential layers that touch
only private state port to the concurrent setting directly. Lesson: an interface that is a
first-class object with its own proof obligations is what makes layers reusable.

**AWS, other** [P unless marked]. *Cedar* (Lean, FSE 2024 industry track, arXiv 2407.01688):
"verification-guided development" -- an executable Lean model (1,673 LOC) with proofs (5,714 LOC)
of properties such as forbid-trumps-permit and validator soundness, and differential random testing
of the 15,693-line Rust implementation against the model; proofs found 4 bugs, DRT and property
testing 21. Lesson: prove on a small model and connect it to the real artefact by testing, which
decouples proof effort from implementation churn. *Nitro Isolation Engine*: §2.1 above.
*s2n-bignum* (HOL Light, verified assembly): §3 [S]. *Zelkova* (SMT-based IAM policy analysis, FMCAD
2018): not fetched, nothing claimed [U].

---

## 5. Lessons for AutoDecompose (evidence-backed rules)

Each rule names the AutoDecompose quantity it bears on: tokens per closed leaf (cost), decomposition
correctness r, leaf closure by automation p, subagent success q (note §4-§6).

1. **Generate most child statements mechanically from the structure of the parent; reserve humans
   (or the planner model) for the few statements that carry the idea.** seL4's proof "decomposes
   along function boundaries", and its tools generated about three quarters of all lemmas (95,000
   vs 22,000 human-stated, Bourke 2012) [P]; `crunch` derives `P ⊢ g` for every callee `g` of `f`
   and closes them with `wp`/`simp` [P]; AutoCorrode derives a WP obligation per function contract
   and uses callee contracts as lemmas [P]; CompCert and CakeML fix one statement shape per pass [P].
   For mathematics the analogue of the call graph is the definitional and inductive structure of the
   statement (cases, induction steps, unfolding of each defined constant). Bears on r and on
   tokens: generated statements cost no planner tokens.

2. **Separate the global "invariant" from the local steps, and fix it before fanning out.** In
   seL4 invariants took 80 % of refinement-1 effort, design-level parallelism worked only "once the
   formulation of invariants had stabilized", and starting the next stage early "may negate" the
   savings (SOSP §5.2; Andronick 2012) [P]. Write the precise invariant at once rather than growing
   a simple one (Cock 2008) [P]. Vero's residual failures cluster around "a few missing invariants"
   needing "inductive generalization ... not additional proof attempts" [P]. For AutoDecompose: the
   strengthened induction hypothesis or key auxiliary statement is the invariant; it should be
   produced and disproof-checked in Stage 0-1 before any student is scheduled.

3. **Freeze the top-level statement first, give agents proof bodies only, and check integration
   continuously.** Bourke 2012: "state the final top-level theorem first" and run continuous
   regression to catch "an overly weak statement in one sub-proof" early [P]. CAPRI: 6 of 144
   Isabelle-accepted repairs had edited protected text; restricting to proof bodies removed this at
   a cost of 2 of 36 repairs [P]. The Nitro MRS generates both code and Isabelle definitions from one
   source [P]. This is Prove2Me's immutable statement object; the evidence says enforce it
   mechanically, not by instruction.

4. **Aim for short leaves: the bulk of a large verification is one-to-ten-step lemmas.** FVELer:
   41.5 % of 29,125 seL4 lemmas are one step, 86 % at most ten [P]; l4v median 8 lines per lemma,
   p90 28 [P, measured]; mean 11-16 lines per lemma in Matichuk's seL4 sets (my arithmetic) [P];
   CompCert passes are 1,500-3,000 lines each, i.e. many small lemmas [P]. Matches Aristotle's "very
   short proof" rule [B §C2]. A student budget of tens of turns per leaf is consistent with this;
   a leaf needing hundreds of lines is a decomposition failure, not a student failure.

5. **Predict leaf cost from statement size, and keep statements minimal.** Proof size grows
   quadratically with the number of distinct definitions a statement mentions (R² up to 0.937 with
   the idealised measure), and effort grows linearly with proof size (3.35 person-weeks per 1,000
   lines plus a 10-week overhead, R² 0.914) [P, Matichuk 2015; Staples 2014]. Over-specified
   statements (mentioning large constants needlessly) distort this. Two uses: (a) a testable
   prediction for AutoDecompose -- tokens per closed leaf should scale roughly with the square of the
   leaf's idealised statement size; (b) a rule -- a decomposition template should abstract every
   constant the child does not need (generalise before proving), which Klein also lists as an
   automation target [P].

6. **Prove at the most abstract level the statement allows; let refinement or instantiation carry it
   down.** seL4's refinement 1 (8 py) carried the semantics so refinement 2 (3 py) needed no C
   invariants; integrity on the abstract spec took 7.4 pm against an estimated ≥20 py on C (TOCS)
   [P]; AutoCorres cut spec size 25-53 % [P]; CertiKOS layers turn the task into "many simple and
   easily automatable ones" [P]; CakeML adds an IL whenever a feature is compiled away [P]. For
   mathematics: state lemmas over the weakest structure that suffices, then instantiate.

7. **Pair each decomposition rule with its own closing automation; a general hammer only takes the
   shallow tail.** Sledgehammer alone closes 40.3 % of seL4 theorems but 15.0 % of proof lines
   (OSDI'26) [P]; the bulk of l4v is closed by domain tactics (`wp`, `wpsimp`, `crunch`, `corres`
   splitting: ~21,800 `wp`-family invocations) [P, measured]; Crush runs "hundreds of iterations"
   of an ordered branch disjunction, deliberately excluding `force`/`blast`/`auto`, and "a bare
   apply crush is rarely getting far" without configuration [P]. For AutoDecompose: a template that
   emits, say, an induction skeleton should also emit the method that closes its routine cases
   (`induct ... ; auto simp: ...`), and only the residue goes to `fill_sorries` and students. This
   extends [B §E rule 5]'s ladder with a rule-specific first rung.

8. **Ship every leaf with its context, stubbed dependencies and named facts.** VeruSAGE's unit is one
   function with dependencies extracted and dependent proofs stubbed as `external_body` [P];
   AutoReal needed hand-supplied context, and context plus training moved 1/105 to 57/105 [P]; in
   the OSDI'26 search 60.1 % of step errors were "undefined fact" [P]; KVerus concludes that
   cross-file context is required [S]. Prove2Me's sketch-importing-open-children is the same object.
   Bears on q.

9. **Check every generated statement for truth and for lost context before any proof effort.** In
   the OSDI'26 evaluation 23 of 241 unsolved lemmas were genuinely false because assumptions were
   dropped when the benchmark sliced scripts [P]; Sonnet 4.5 found five wrong lemma specifications in
   unfinished Atmosphere proofs [P]; "Just Type It" found misaligned statements in review [P]; seL4's
   first refinement forced ~500 spec changes, half of them bug fixes (SOSP §5.2) [P]. Extraction of
   a child from its parent is itself an error source, so r must be measured on the extraction, not
   only on the planner's text. Complements [B §E rule 4] and [C §3].

10. **Expect within-development helper lemmas to dominate, and share them across siblings.** Vero:
    helpers hold a median 73.6 % of proof lines and are shared by at least two specifications in 80
    of 82 full solves [P]; seL4's lifting lemmas and de-duplication guide exist because copied
    helpers double maintenance [P]. This does not contradict the absence of cross-*problem* reuse
    [B §C7]: reuse pays inside one decomposition. The scheduler should deduplicate equivalent
    children (`solve_direct` on new statements) before dispatch.

11. **Bound fan-out by interface stability, not by worker count.** About four people worked
    concurrently "without much conflict" on 10 kLOC; beyond five or six "a more serious effort in
    planning and synchronisation" was needed (Cock 2008) [P]; up to six on one module (Bourke 2012)
    [P]; Everest's two-step proof style exists to let two people work in parallel, and its worst
    social cost was one developer's change breaking another's proof (TOPLAS 2026) [P]; Staples found
    no significant team-size effect on productivity [P]. Prove2Me's serialised merge queue [note §6]
    is the large-scale version. Parallelise only over children whose statements are frozen.

12. **Price revisions by how far they cut across existing statements.** A local change re-verifies
    at roughly 3-5 times its code cost; a cross-cutting change of <5 % of the code cost 17 % of the
    original proof effort, and interrupts/page tables cost 32 % (SOSP §5.3; Andronick 2012) [P].
    L4.verified's proof cache and AutoCorrode's I/C re-check only lemmas whose dependencies changed
    [P]. For Stage 4 (revise the blueprint): adding a lemma is cheap, changing a shared definition or
    the invariant invalidates its whole cone; log revisions by type so the cost model can separate
    them.

13. **Count success by weight, not by number of theorems.** 77.6 % of seL4 theorems was 36.2 % of
    proof lines (OSDI'26) [P]; VeruSAGE success falls with task size [P]. AutoDecompose should report
    tokens per closed leaf alongside leaf size (statement size per rule 5, or the reference proof
    length), otherwise a harness that closes only short leaves looks efficient.

14. **Make the verifier's answers unambiguous in scope and cheap to repeat.** AutoCorrode's agents
    moved on after `commands_failed: 0` that counted only the edited range, while downstream proofs
    were broken; the fix split edit-scoped from file-scoped counts [P]. Identical tool calls 60+
    times led to loop detection [P]. IronFleet keeps leaf feedback at 1-10 s and farms out file
    checks [P]; Everest prefers small resource limits for stability [P]. These match [B §E rules 9,
    15-16] and the pass-1 give-up loops (note §1).

---

## 6. Gaps and unverified items

- **No person-years for AutoCorrode or the Nitro Isolation Engine** are published; only the 330,000
  line figure. The local AutoCorrode history begins with a squashed import (2025-03-30), so its
  development before that date is not visible.
- **Whether AutoCorrode commits were agent-written** cannot be determined; there are no trailers.
  `CLAUDE.md` and `MCP.md` in the local clone are untracked local files, not upstream.
- **Who decided the seL4 partition** is stated only collectively ("the FM team managed to design
  refinement calculi ... that allowed the work to be divided"); no per-person allocation data were
  found beyond Staples 2014's team sizes.
- **The number of lemmas `crunch` generates today** cannot be counted without building l4v; 2,136
  top-level targets (single architecture) is a lower bound. The 95,000 tool-generated-inclusive
  count is from 2012.
- **My lemma-length measurement** is textual (lines to the next top-level command, blank lines
  included, indented lemmas inside proofs ignored); treat the median and percentiles as indicative.
- **Effort discrepancy**: SOSP/TOCS give 11 py seL4-specific plus 9 py tools; Klein FM 2014 gives 12
  plus 12-13. TOCS's table is the more careful (partly from weekly records).
- **Selene's own numbers** (27.06 %, "nearly 40 %" one-line) are second-hand via AutoReal and the
  OSDI'26 paper; its abstract gives none.
- **[S] items**: AlphaVerus, SAFE, RagVerus/RVBench, KVerus, the vericoding benchmark, Laurel and
  s2n-bignum-bench were read through search summaries or abstracts only.
- **Not fetched**: Zelkova (FMCAD 2018); the CompCert/Csmith bug study; DafnyBench; the IronFleet
  companion Ironclad paper; Jeffery et al. 2015 research agenda (downloaded, not read).
- **No study found** that applies an LLM agent to proof *maintenance* of seL4 across kernel versions,
  or that measures agent productivity in lines of proof per token on any industrial development.
- Paulson's AITP slides carry no date in the extracted text.

---

## Source index

seL4 and l4v
- Klein et al., seL4: Formal verification of an OS kernel, SOSP 2009: https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf
- Klein et al., Comprehensive formal verification of an OS microkernel, TOCS 32(1) 2014: https://trustworthy.systems/publications/nicta_full_text/7371.pdf
- Cock, Klein, Sewell, Secure microkernels, state monads and scalable refinement, TPHOLs 2008: https://trustworthy.systems/publications/nicta_full_text/483.pdf
- Andronick et al., Large-scale formal verification in practice: a process perspective, ICSE 2012: https://trustworthy.systems/publications/nicta_full_text/5396.pdf
- Bourke, Daum, Klein, Kolanski, Challenges and experiences in managing large-scale proofs, CICM 2012: https://trustworthy.systems/publications/nicta_full_text/5717.pdf
- Klein, Proof engineering considered essential, FM 2014 (sole author): https://trustworthy.systems/publications/nicta_full_text/7923.pdf
- Klein, Proof engineering challenges for large-scale verification, 2014: https://trustworthy.systems/publications/nicta_full_text/8066.pdf
- Staples et al., Productivity for proof engineering, ESEM 2014: https://trustworthy.systems/publications/nicta_full_text/8105.pdf
- Matichuk et al., Empirical study towards a leading indicator for cost of formal software verification, ICSE 2015: https://trustworthy.systems/publications/nicta_full_text/8318.pdf
- Greenaway, Lim, Andronick, Klein, Don't sweat the small stuff (AutoCorres), PLDI 2014: https://trustworthy.systems/publications/nicta_full_text/7629.pdf
- l4v repository and docs: https://github.com/seL4/l4v ; https://github.com/seL4/l4v/tree/master/docs ; crunch: https://github.com/seL4/l4v/blob/master/lib/crunch-cmd.ML
- seL4 Summit 2026 abstracts: https://sel4.systems/Summit/2026/abstracts2026.html

AI on seL4 and Isabelle developments
- FVEL / FVELer: https://arxiv.org/html/2406.14408v2
- Selene: https://arxiv.org/abs/2401.07663
- AutoReal: https://arxiv.org/html/2602.08384v1
- Neuro-symbolic proof generation (OSDI'26): https://arxiv.org/html/2603.19715v2 ; code https://github.com/SoaringE/seL4-proof-search
- CAPRI: https://arxiv.org/abs/2608.13459
- Just Type It in Isabelle!: https://arxiv.org/html/2604.15713v3
- Paulson, AI and Isabelle (AITP slides): https://aitpm.github.io/slides/Paulson.pdf

AutoCorrode and AWS
- AutoCorrode: https://github.com/awslabs/AutoCorrode (local clone, HEAD 2026-06-15: README, AUTHORS, design-documents/00-10, Crush/, Micro_Rust_Examples/{Showcase,Crush_Examples}.thy, iq/, ir/, ic/, isabelle-assistant/{README,prompts}, git log)
- Nitro Isolation Engine, ITP 2026 invited talk: https://drops.dagstuhl.de/storage/00lipics/lipics-vol382-itp2026/LIPIcs.ITP.2026.1/LIPIcs.ITP.2026.1.pdf
- Nitro Isolation Engine whitepaper: https://d1.awsstatic.com/onedam/marketing-channels/website/aws/en_US/whitepapers/compliance/nitro-isolation-engine-whitepaper.pdf
- Cedar, verification-guided development: https://arxiv.org/abs/2407.01688
- s2n-bignum-bench: https://arxiv.org/abs/2603.14628

Verus, Dafny, Lean, F\* at project scale
- VeruSAGE: https://arxiv.org/html/2512.18436v2 ; benchmark https://github.com/microsoft/verus-proof-synthesis
- Vero: https://arxiv.org/html/2608.13522
- AutoVerus: https://arxiv.org/abs/2409.13082 ; AlphaVerus: https://arxiv.org/abs/2412.06176 ; SAFE: https://arxiv.org/abs/2410.15756
- RagVerus: https://arxiv.org/abs/2502.05344 ; repository-level follow-up: https://arxiv.org/abs/2509.25197 ; KVerus: https://arxiv.org/abs/2605.03822
- Vericoding benchmark: https://arxiv.org/abs/2509.22908
- Laurel: https://arxiv.org/abs/2405.16792
- Goedel-Code-Prover: https://arxiv.org/abs/2603.19329

Other projects
- Leroy, Formal verification of a realistic compiler, CACM 2009: https://xavierleroy.org/publi/compcert-CACM.pdf
- Tan et al., The verified CakeML compiler backend, JFP 2019: https://cakeml.org/jfp19.pdf
- Hawblitzel et al., IronFleet, SOSP 2015: https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf
- Ahman et al., Project Everest: perspectives from developing industrial-grade high-assurance software, TOPLAS 48(2) 2026: https://mtzguido.github.io/pubs/everest.pdf
- Gu et al., Building certified concurrent OS kernels (CertiKOS), CACM 2019: https://flint.cs.yale.edu/flint/publications/cacm19.pdf
