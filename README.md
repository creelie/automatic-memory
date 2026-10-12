# The sl(2) weight system at c = -3/32 extends to a graph 4-invariant

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).

This repository proves the conjecture of Fomichev, Karev, Pavutnitskiy and
Usanov ([arXiv:2607.24217](https://arxiv.org/abs/2607.24217), Section 4):

> The specialization of the sl(2)-weight system at c = -3/32 extends to a
> 4-invariant of graphs.

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
| `paper/` | LaTeX source (`main.tex`, `refs.bib`, Elsevier `elsarticle` class and style) and the compiled `main.pdf` |
| `lean/` | Lean 4 + Mathlib formalization (16 files, 4120 lines); `SL2W/Main.lean` holds `SL2W.main_theorem` |
| `checks/python/` | `check.py`: exact check of the theorem; `proof_steps.py`: exact check of every intermediate identity of the proof |
| `checks/julia/` | exact check in Julia |
| `checks/c/`, `checks/cpp/` | checks modulo 2^61 - 1 in C and C++, including the values tabulated by Fomichev et al. (`checks/data/`) |
| `run_all.sh` | runs the Lean build, the axiom check and all programs |
| `journal/JOURNAL.md` | target journal, format rules and AI policy |
| `dist/` | the paper PDF, the arXiv tarball and `MasterSl2WeightSystemAtMinus3Over32Zip.zip`, which holds every file of the repository |

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

To build the paper: `cd paper && latexmk -pdf main.tex`.

## Archive

Zenodo, all versions: [10.5281/zenodo.23312529](https://doi.org/10.5281/zenodo.23312529);
release v1.0.0: [10.5281/zenodo.23312530](https://doi.org/10.5281/zenodo.23312530).

## License

MIT, see `LICENSE`.
