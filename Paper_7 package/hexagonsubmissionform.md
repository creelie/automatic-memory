# Hexagon submission fields

Submit a replacement version of 2610.00320v1; do not create a duplicate work.
The new version identifier is assigned by Hexagon after submission and is not
asserted in advance. Existing record: https://hexagonmath.org/2610.00320v1

## Title

The sl(2) weight system at c = -3/32 extends to a graph 4-invariant

## Abstract - copy the complete block

We prove unconditionally the conjecture of Fomichev, Karev, Pavutnitskiy and Usanov that the specialization of the $\mathfrak{sl}(2)$ weight system at $c=-3/32$ extends to a $4$-invariant of graphs. The extension is $\xi(G)=(-32)^{-n}S_G(-2)$, where $S_G(N)$ counts with signs the assignments of $2$-element subsets of $\{1,\dots,N\}$ to the $n$ vertices of $G$.

The block uses explicit TeX commands rather than macros defined only in main.tex.

## Subjects, tags and MSC2020

Primary subject: math.CO
Cross-list subjects: math.GT, math.RT
Tags: weight systems, graph four-term relations, oscillator representation, Clifford algebra, finite type knot invariants, Lean formalization
MSC2020 primary code: 05C31
MSC2020 additional codes: 57K16, 17B10, 15A66
arXiv identifier: leave blank. No arXiv identifier is asserted.

## Contributors - preserve this order

Contributor 1: Deep Bhattacharjee
Affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; Formerly, University of Calcutta, Kolkata 700073, India
ORCID: 0000-0003-0466-750X

Contributor 2: Ushashi Bhattacharya
Affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan
ORCID: 0009-0002-2254-3914

The affiliations are former affiliations, not assertions of current employment.

## Authorship and understanding selections

Text: A mix of human-written and AI-generated.
Human understanding: Some parts of this contribution, but not all, have been checked and understood by a human.
The text classification and human-understanding field follow the existing Paper 7 preprint; review any update before submission.

## Provenance statement - copy this paragraph

Claude (Anthropic) assisted the original mathematical exploration, proof, text, figures, Lean development and checking code. OpenAI Codex assisted this revision's proof and definition audit, elementary faithful-action argument, literature checks, verification records and submission files. These uses include research and writing assistance. The human authors retain responsibility for the final mathematics and submission decisions. The recorded human-understanding declaration is: Some parts of this contribution, but not all, have been checked and understood by a human. The human authors retain responsibility for the content.
The universal extension theorem and its matrix-trace definition are formalized in Lean 4.34.1 with pinned Mathlib. At the unchanged proof-source commit, the complete build and four endpoint axiom reports passed with only propext, Classical.choice and Quot.sound. Python exact checks were rerun locally; Julia, C and C++ passed in the archived full run. The grouping proof for part (a) and the added faithful-action lemma are supplied in the written argument; no new formalization of the abstract Weyl algebra is claimed.

## Tools used

- Anthropic Claude / Claude Code
- OpenAI Codex
- Lean 4.34.1 / Mathlib
- Python
- Julia
- C and C++
- LaTeX / pdfLaTeX

Use the corresponding system/tool entry if available and Other for an unlisted
tool. Do not invent a model version for an entry that is not documented.

## Formalisation links

https://github.com/creelie/automatic-memory/blob/v2.2.0/lean/SL2W/Main.lean
https://github.com/creelie/automatic-memory/tree/v2.2.0/lean

Scope: The universal extension theorem and its matrix-trace definition are formalized in Lean 4.34.1 with pinned Mathlib. At the unchanged proof-source commit, the complete build and four endpoint axiom reports passed with only propext, Classical.choice and Quot.sound. Python exact checks were rerun locally; Julia, C and C++ passed in the archived full run. The grouping proof for part (a) and the added faithful-action lemma are supplied in the written argument; no new formalization of the abstract Weyl algebra is claimed.
If the portal rejects a host/path, leave it for manual review rather than
uploading Lean material in the article source ZIP.

## Files and licence

Required source ZIP: Sl2_weight_system_at_minus_3_over_32_graph_4_invarianttex.zip
Reference PDF: Sl2_weight_system_at_minus_3_over_32_graph_4_invariant.pdf
AI provenance upload: AI_PROVENANCE.md (outside the source ZIP).
Licence selection: CC BY 4.0, matching the existing Hexagon manuscript record.
The manuscript source ZIP contains the article, bibliography and required
figures only. It excludes Lean developments, executables, journal correspondence,
other manuscripts and private model traces. Standard TeX Live classes/packages
are build dependencies rather than relicensed files in this ZIP.

## Review before submitting

Use pdfLaTeX, main document main.tex. The extracted ZIP was rebuilt locally and
its full extracted text and page count matched the supplied PDF. Confirm the
rendered title, abstract, byline, references and final portal preview. This
packet does not press the portal's Process or Submit button on the author's behalf.
