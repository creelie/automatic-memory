Deep Bhattacharjee and Ushashi Bhattacharya, *The sl(2) weight system at c = -3/32 extends to a graph 4-invariant*.

The paper proves the conjecture of Fomichev, Karev, Pavutnitskiy and Usanov (arXiv:2607.24217,
Section 4): the specialization of the sl(2) weight system at c = -3/32 extends to a 4-invariant
of graphs, namely xi(G) = (-32)^{-n} S_G(-2), where S_G(N) counts with signs the assignments of
2-element subsets of {1, ..., N} to the n vertices of G.

Lean 4 with Mathlib checks both parts of the theorem (SL2W.main_theorem); it depends only on
propext, Classical.choice and Quot.sound. Programs in Python, Julia, C and C++ check the theorem
and every step of the proof on small cases. This release runs all of them, Lean included.

Files: the paper (`Sl2WeightSystemAtMinus3Over32_final2.pdf`), its LaTeX source with the figures
as PNG (`Sl2WeightSystemAtMinus3Over32_final2-tex.zip`) and the arXiv tarball
(`Sl2WeightSystemAtMinus3Over32_final2-arxiv.tar.gz`). The archive of the tag holds the Lean
project, the check programs and the master zip `MasterSl2WeightSystemAtMinus3Over32_masterzipfinal2.zip`.
