# AI provenance: The sl(2) weight system at c = −3/32 extends to a graph 4-invariant

Authors: Deep Bhattacharjee (corresponding author, ORCID 0000-0003-0466-750X;
formerly EGSPL, Bhubaneswar, Odisha 751030, India, and formerly University of
Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal,
India) and Ushashi Bhattacharya (ORCID 0009-0002-2254-3914; formerly National
Taiwan University, Taipei 106319, Taiwan).

- Paper: https://github.com/creelie/automatic-memory/blob/main/preprintSl2WeightSystemAtMinus3Over32/Sl2WeightSystemAtMinus3Over32.pdf
- Lean formalization and code: doi:10.5281/zenodo.23384025 (release v2.0.0; all versions doi:10.5281/zenodo.23312529)
- Repository: https://github.com/creelie/automatic-memory

## Result

Fomichev, Karev, Pavutnitskiy and Usanov conjectured that the sl(2) weight
system, specialised at c = −3/32, extends to a 4-invariant of graphs
(arXiv:2607.24217, Section 4). The paper proves this conjecture.

- It gives an explicit graph invariant ξ(G) = (−32)^(−n) S_G(−2), where
  S_G(N) counts with signs the assignments of 2-element subsets of
  {1, ..., N} to the n vertices of G, and proves that ξ satisfies the
  four-term relations of graphs.
- It proves that w_D(−3/32) = ξ(Γ(D)) for every chord diagram D, where Γ(D)
  is the intersection graph of D.

## Who did what

Deep Bhattacharjee chose the problem, directed the work, set the format and
the target journal, and ran the computations. Claude (Anthropic), used through
Claude Code under his direction, produced the following:

- the proof (Verma modules, the oscillator representation with a supertrace,
  the expansion over matchings, the Clifford trace, and the involution for
  the four-term relation);
- the Lean 4 formalization (16 files, 4120 lines);
- the checking programs in Python, Julia, C and C++;
- the figures;
- the LaTeX text of the paper, its footnotes and its reference list (every
  reference, the three self-citations included, was checked against the
  publisher's or Crossref's record);
- this file and the submission notes.

No other AI system took part. The paper uses no unproved result from other
work.

## How the result is checked

- **Lean 4.34.1 with Mathlib.** `SL2W.main_theorem` states two things: ξ is a
  4-invariant, and for every chord diagram D the weight system polynomial
  exists and takes the value ξ(Γ(D)) at −3/32. These are parts (b) and (c) of
  the main theorem, the content of the conjecture. The theorem depends only on
  the standard axioms propext, Classical.choice and Quot.sound. There is no
  `sorry`, `native_decide` or added axiom.
- **Independent programs.**
  - Python and Julia check the theorem in exact arithmetic on all chord
    diagrams with at most five chords and on random larger ones.
  - A second Python program checks every intermediate identity of the proof.
  - C and C++ programs check modulo 2^61 − 1 on all 11,465 chord diagrams
    with at most six chords and on random diagrams with seven and eight
    chords, and reproduce the values tabulated by Fomichev et al. on 63
    graphs with nine and ten vertices.
- **Release workflow.** It builds the Lean proof, checks its axioms and runs
  every program before publishing.

## What is not claimed

Part (a) of the main theorem, the binomial expansion of S_G(N), is proved by
hand and is not in the Lean file; it is not part of the conjecture. No
statement of the paper rests on a floating-point computation. The authors
checked on 15 October 2026, and again on 17 October 2026, that the
conjecture is stated as open in the preprint of Fomichev, Karev,
Pavutnitskiy and Usanov and found no other proof on arXiv, on GitHub or on
the web; the earlier value c = 3/8 was settled by Fomichev and Karev and by
Yan, Deng and Jin, and is credited to them.
