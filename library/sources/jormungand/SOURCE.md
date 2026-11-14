# Source: jormungand

- Repository: https://github.com/sel4proj/jormungand
- Commit (pinned 2026-11-14T14:53:36Z): `bad97f9817b4034cd705cd295a1f86af880a7631`
- Browse at this commit: https://github.com/sel4proj/jormungand/tree/bad97f9817b4034cd705cd295a1f86af880a7631
- Language: isabelle
- Licence: `BSD-2-Clause AND GPL-2.0-only`, read from the licence files by fixer (after discovery-2) (per file: the top-level LICENSE_BSD2.txt covers jormungand's own theories, but the vendored case_study/l4v/ tree ships LICENSE_GPLv2.txt (copied here) and its files carry headers such as 'This software may be distributed and modified according to the terms of the GNU General Public License version 2 ... @TAG(NICTA_GPL)' (e.g. case_study/l4v/sys-init/InitCSpace_SI.thy lines 1-8); each file's header governs); the detector had `BSD-2-Clause`. The licence text below governs.
- Licence recorded: 2026-11-14T16:19:07Z
- How found: discovery-2: B-isabelle, discovery-1:B-isabelle

## Licence files

- [LICENSE_BSD2.txt](https://github.com/sel4proj/jormungand/blob/bad97f9817b4034cd705cd295a1f86af880a7631/LICENSE_BSD2.txt) (copied here as `upstream-LICENSE_BSD2.txt`)
- [case_study/l4v/LICENSE_GPLv2.txt](https://github.com/sel4proj/jormungand/blob/bad97f9817b4034cd705cd295a1f86af880a7631/case_study/l4v/LICENSE_GPLv2.txt) (copied here as `upstream-case_study--l4v--LICENSE_GPLv2.txt`)

## Attribution

Code under `library/entries/*/code/` whose entry names this source is copied verbatim from the repository above at the pinned commit, under its licence. Copyright remains with its authors.

## Note

Isabelle/HOL theories for Backwards and Forwards with Separation Logic: Hoare and strongest-postcondition separation-logic tactics plus a capDL-api/sys-init case study built from framed separation-logic lemmas.
