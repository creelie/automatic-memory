import SL2W.Osc
import SL2W.FourT

/-!
# Main theorem

The `sl(2)` weight system, written as a polynomial in `c = (d² - 1)/8`, takes at
`c = -3/32` the value `ξ` of the intersection graph, and `ξ` is a `4`-invariant of graphs.
Hence the `sl(2)` weight system at `c = -3/32` extends to a graph `4`-invariant.
-/

open Polynomial

namespace SL2W

lemma infinite_c_values : Set.Infinite ((fun d : ℕ => (((d : ℚ) ^ 2 - 1) / 8)) '' Set.Ici 1) := by
  refine (Set.Ici_infinite 1).image ?_
  intro d₁ _ d₂ _ h
  simp only at h
  have h' : ((d₁ ^ 2 : ℕ) : ℚ) = ((d₂ ^ 2 : ℕ) : ℚ) := by push_cast; linarith
  exact Nat.pow_left_injective two_ne_zero (by exact_mod_cast h')

/-- For every chord diagram `D` the `sl(2)` weight system `d ↦ W d D` is the restriction of a
unique polynomial `P` in `c = (d² - 1)/8`, and `P(-3/32) = ξ(Γ(D))`; the graph invariant `ξ`
satisfies the four-term relations. -/
theorem main_theorem : IsFourInvariant (fun G => ξ G) ∧ ∀ (n : ℕ) (D : ChordDiagram n),
    (∃ P : Polynomial ℚ, ∀ d : ℕ, 1 ≤ d → P.eval (((d : ℚ) ^ 2 - 1) / 8) = W d D) ∧
    ∀ P : Polynomial ℚ, (∀ d : ℕ, 1 ≤ d → P.eval (((d : ℚ) ^ 2 - 1) / 8) = W d D) →
      P.eval (-3 / 32) = ξ D.interGraph := by
  refine ⟨ξ_isFourInvariant, fun n D => ⟨⟨D.wsPoly, D.wsPoly_eval_W⟩, fun P hP => ?_⟩⟩
  have hPeq : P = D.wsPoly := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine infinite_c_values.mono ?_
    rintro _ ⟨d, hd, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hP d hd, D.wsPoly_eval_W d hd]
  rw [hPeq, show (-3 / 32 : ℚ) = (((-1 / 2 : ℚ) + 1) ^ 2 - 1) / 8 by norm_num, D.wsPoly_eval,
    D.lam_half]

end SL2W
