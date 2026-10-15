# The sl(2) weight system at c = -3/32 extends to a graph 4-invariant

**Deep Bhattacharjee** (corresponding author), Formerly, Electro-Gravitational
Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
(itsdeep@live.com, d.bhattacharjee@erl-forschung.de;
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X))

**Ushashi Bhattacharya**, Formerly, National Taiwan University, Taipei 106319,
Taiwan (rai.bhattacharya.in@gmail.com;
ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914))

The paper proves the conjecture of Fomichev, Karev, Pavutnitskiy and Usanov
([arXiv:2607.24217](https://arxiv.org/abs/2607.24217), Section 4):

> The specialization of the sl(2)-weight system at c = -3/32 extends to a
> 4-invariant of graphs.

- Paper: [`preprintSl2WeightSystemAtMinus3Over32/Sl2WeightSystemAtMinus3Over32.pdf`](preprintSl2WeightSystemAtMinus3Over32/Sl2WeightSystemAtMinus3Over32.pdf)
- Lean 4 formalization on Zenodo (release v2.0.0): doi:[10.5281/zenodo.23384025](https://doi.org/10.5281/zenodo.23384025); all versions: doi:[10.5281/zenodo.23312529](https://doi.org/10.5281/zenodo.23312529)
- Master zip: [`MasterSl2WeightSystemAtMinus3Over32_masterzipfinal2.zip`](https://github.com/creelie/automatic-memory/raw/main/MasterSl2WeightSystemAtMinus3Over32_masterzipfinal2.zip)
- Target journal: European Journal of Combinatorics (`journal/JOURNAL.md`)
- MSC 2020: Primary 05C31; Secondary 57K16, 17B10, 15A66

## Result

For a graph G = (V, E) with n vertices and N >= 0 let

    S_G(N) = sum over p : V -> {2-element subsets of {1..N}} of
             prod over edges xy of (-1)^{|p(x) ∩ p(y)|}

and let T_k(G) be the same sum over the maps p whose images cover exactly
{1, ..., k}. Then S_G(N) = sum_k C(N, k) T_k(G) is a polynomial in N, and

    xi(G) = S_G(-2) / (-32)^n = (-32)^{-n} sum_{k=0}^{2n} (-1)^k (k+1) T_k(G).

**Theorem.** xi satisfies the four-term relations of graphs, and for every
chord diagram D the sl(2) weight system w_D (a polynomial in the Casimir c)
satisfies w_D(-3/32) = xi(Γ(D)), where Γ(D) is the intersection graph.

Examples: xi(K_1) = -3/32, xi(K_2) = 57/1024.

The proof lets the chord element C_D act on Verma modules, realizes the
Verma modules of highest weights -1/2 and -3/2 in the oscillator
representation, evaluates the resulting scalar with a supertrace on the Weyl
algebra and a Wick formula, and identifies the sum over matchings with a trace
in the Clifford algebra; the four-term relation follows from an involution on
the maps p.

## Contents

| Path | Contents |
|---|---|
| `preprintSl2WeightSystemAtMinus3Over32/` | the paper as a PDF, the only file in the folder |
| `paper/` | LaTeX source (`main.tex`, `refs.bib`, `main.bbl`, Elsevier `elsarticle` class and style) and the figures as PNG in `paper/figures/` |
| `figures/` | TikZ sources of the three figures and `make_figures.sh`, which writes the PNG files |
| `dist/` | the paper (`Sl2WeightSystemAtMinus3Over32_final2.pdf`), the LaTeX source zip with the figures as PNG (`..._final2-tex.zip`) and the arXiv tarball (`..._final2-arxiv.tar.gz`) |
| `MasterSl2WeightSystemAtMinus3Over32_masterzipfinal2.zip` | every file of the repository with `dist/` and the preprint folder |
| `lean/` | Lean 4 + Mathlib formalization (16 files, 4120 lines); `SL2W/Main.lean` holds `SL2W.main_theorem` |
| `checks/python/` | `check.py`: exact check of the theorem; `proof_steps.py`: exact check of every intermediate identity of the proof |
| `checks/julia/` | exact check in Julia |
| `checks/c/`, `checks/cpp/` | checks modulo 2^61 - 1 in C and C++, including the values tabulated by Fomichev et al. (`checks/data/`) |
| `run_all.sh` | runs the Lean build, the axiom check and all programs |
| `make_dist.sh` | builds the paper, `dist/`, the preprint folder and the master zip |
| `journal/JOURNAL.md` | target journal, format rules and AI policy |
| `.github/workflows/release.yml` | runs every check, Lean included, and publishes a release |

## Lean statement

```lean
theorem main_theorem : IsFourInvariant (fun G => ξ G) ∧ ∀ (n : ℕ) (D : ChordDiagram n),
    (∃ P : Polynomial ℚ, ∀ d : ℕ, 1 ≤ d → P.eval (((d : ℚ) ^ 2 - 1) / 8) = W d D) ∧
    ∀ P : Polynomial ℚ, (∀ d : ℕ, 1 ≤ d → P.eval (((d : ℚ) ^ 2 - 1) / 8) = W d D) →
      P.eval (-3 / 32) = ξ D.interGraph
```

`W d D` is tr(C_D)/d on the d-dimensional irreducible representation, so the
second conjunct says that w_D exists and that w_D(-3/32) = xi(Γ(D)).
`#print axioms SL2W.main_theorem` reports `[propext, Classical.choice,
Quot.sound]`; there is no `sorry`, `admit` or added axiom.

## Running the checks

Requirements: elan (Lean 4.34.1, fetched from `lean/lean-toolchain`),
python3, julia, a C compiler and a C++17 compiler.

    ./run_all.sh            # Lean build (with the Mathlib cache), axiom check, all programs
    ./run_all.sh --no-lean  # programs only

To build the paper and the release files: `./make_dist.sh` (needs latexmk,
zip and tar; `figures/make_figures.sh` redraws the figures).

## Archive

| Release | Zenodo DOI |
|---|---|
| v2.0.0 (two authors, journal format; cited by the paper) | [10.5281/zenodo.23384025](https://doi.org/10.5281/zenodo.23384025) |
| v1.0.1 | [10.5281/zenodo.23312664](https://doi.org/10.5281/zenodo.23312664) |
| v1.0.0 | [10.5281/zenodo.23312530](https://doi.org/10.5281/zenodo.23312530) |
| all versions | [10.5281/zenodo.23312529](https://doi.org/10.5281/zenodo.23312529) |

## License

The code is under the MIT license (`LICENSE`), copyright Deep Bhattacharjee.
The paper in `paper/` and the preprint folder is by Deep Bhattacharjee and
Ushashi Bhattacharya.
