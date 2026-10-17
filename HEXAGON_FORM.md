# Hexagon submission fields

Title: The sl(2) weight system at c = -3/32 extends to a graph 4-invariant

Abstract: We prove unconditionally the conjecture of Fomichev, Karev, Pavutnitskiy and Usanov that the specialization of the sl(2) weight system at c = -3/32 extends to a 4-invariant of graphs. The extension is xi(G) = (-32)^{-n} S_G(-2), where S_G(N) counts with signs the assignments of 2-element subsets of {1, ..., N} to the n vertices of G.

Primary subject: math.CO (Combinatorics)
Cross-list subjects: math.GT (Geometric Topology), math.RT (Representation Theory)
Tags: weight system, intersection graph, four-term relation, oscillator representation, Clifford algebra
MSC2020: 05C31 Graph polynomials; 57K16 Finite-type and quantum invariants, topological quantum field theories (TQFT); 17B10 Representations of Lie algebras and Lie superalgebras, algebraic theory (weights); 15A66 Clifford algebras, spinors; 68V15 Theorem proving (automated and interactive theorem provers, deduction, resolution, etc.)

Contributor 1 (submitting): Deep Bhattacharjee; ORCID 0000-0003-0466-750X; affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India; itsdeep@live.com (second address d.bhattacharjee@erl-forschung.de)
Contributor 2: Ushashi Bhattacharya; ORCID 0009-0002-2254-3914; affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan; rai.bhattacharya.in@gmail.com

Text of the contribution: A mix of human-written and AI-generated.
Human understanding: "All parts" only after both authors have read every proof; otherwise "Some parts, but not all".

Provenance statement: The proofs, the text, the figures, the Lean 4 formalization and the Python, Julia, C and C++ programs were carried out by Deep Bhattacharjee with the help of AI assistance (Claude, Anthropic) in the Claude Code environment. The paper proves the conjecture of D. Fomichev, M. Karev, F. Pavutnitskiy and S. Usanov (arXiv:2607.24217, Section 4) that the sl(2) weight system specialised at c = -3/32 extends to a 4-invariant of graphs, with the explicit extension xi(G) = (-32)^{-n} S_G(-2): the chord element acts on Verma modules, the Verma modules of highest weights -1/2 and -3/2 are realised in the oscillator representation, the resulting scalar is a supertrace on the Weyl algebra computed by a Wick formula, the sum over matchings is a trace in a Clifford algebra, and the four-term relation follows from an involution on the assignments. Both parts of the conjecture, the four-term relation for xi and the identity w_D(-3/32) = xi(Gamma(D)) for every chord diagram D, are proved in Lean 4 with Mathlib (SL2W.main_theorem, 16 files, 4120 lines), depending only on the axioms propext, Classical.choice and Quot.sound, with no sorry, native_decide or added axiom; programs in Python, Julia, C and C++ check the theorem on all chord diagrams with at most six chords and reproduce the values tabulated by Fomichev et al. The binomial expansion of S_G(N) (part (a) of the main theorem) is proved by hand and not formalized. No statement rests on a floating-point computation. The earlier value c = 3/8 is due to Fomichev and Karev and to Yan, Deng and Jin and is credited to them. Both authors approved the final version.

Tools used: Anthropic - Claude (Claude Code); Lean community - Lean 4 (v4.34.1) with Mathlib; Python; Julia; C; C++; shell.
arXiv identifier: none (not posted on arXiv).
Formalization: https://github.com/creelie/automatic-memory/blob/main/lean/SL2W/Main.lean (archived at Zenodo, release v2.0.0: https://doi.org/10.5281/zenodo.23384025)

Source files or ZIP: Sl2WeightSystemAtMinus3Over32_final2-tex.zip (the folder Sl2WeightSystemAtMinus3Over32_final2-tex/ with main.tex, elsarticle.cls and figures/ as PNG; seven entries; compiles with latexmk -pdf main.tex, no BibTeX pass, all fonts embedded). Do not upload the master zip or the Lean files here.
AI provenance files: AI_PROVENANCE_Sl2WeightSystemAtMinus3Over32.md
License: CC BY 4.0

Data availability (in the paper): LaTeX source, the Lean 4 formalization and the programs archived at Zenodo under doi:10.5281/zenodo.23384025 (release v2.0.0; all versions 10.5281/zenodo.23312529); repository https://github.com/creelie/automatic-memory; the folder preprintSl2WeightSystemAtMinus3Over32 holds the PDF only.
AI disclosure (in the paper, Data and code availability): Deep Bhattacharjee carried out the computations and the Lean, Julia, C, C++, Python and shell verifications, and the proofs and the text were drafted, with AI assistance (Claude, Anthropic); both authors approved the final version. No separate AI declaration.
Funding: none. Competing interests: none.
Device folder: D:\Hexagon\02 Sl2WeightSystemAtMinus3Over32.
