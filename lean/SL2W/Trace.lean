import SL2W.Verma

/-!
# The trace in the irreducible representation of dimension `d`

The matrix of a word in `sl2Rep d` is read off the Verma module of highest weight `d - 1`:
the paths leaving the levels `0, …, d - 1` carry a vanishing coefficient. Hence
`W d D = lam (d - 1) 0`.
-/

open Finset Polynomial

namespace SL2W

@[simp] lemma chA_zero : chA 0 = -1 := by simp [chA]
@[simp] lemma chA_one : chA 1 = 1 := by simp [chA]
@[simp] lemma chA_two : chA 2 = 0 := by simp [chA]

lemma sl2Rep_apply (d : ℕ) (a : Fin 3) (r t : Fin d) :
    sl2Rep d a r t = if (r : ℤ) = (t : ℤ) + chA a then coef a ((d : ℚ) - 1) (t : ℕ) else 0 := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp only [sl2Rep, Matrix.of_apply, chA_zero, coef]
    split_ifs with h1 h2 h2 <;> first | ring1 | (exfalso; omega)
  · simp only [sl2Rep, Matrix.of_apply, chA_one, coef]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · simp only [sl2Rep, Matrix.diagonal_apply, chA_two, coef]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exfalso; exact h2 (by subst h1; simp)
    · exfalso; exact h1 (Fin.ext (by omega))
    · rfl

/-- The matrix entries of a word in the representation of dimension `d`. -/
lemma entry_word (d : ℕ) : ∀ (w : List (Fin 3)) (r s : Fin d),
    (w.map (sl2Rep d)).prod r s =
      if (r : ℤ) = (s : ℤ) + ch w then Qf w ((d : ℚ) - 1) (s : ℕ) else 0
  | [], r, s => by
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply, ch_nil, add_zero, Qf]
    by_cases h : r = s
    · subst h; simp
    · rw [if_neg h, if_neg (by omega)]
  | a :: w, r, s => by
    rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
    simp_rw [sl2Rep_apply, entry_word d w]
    rw [Qf_cons, ch_cons]
    by_cases hlo : (s : ℤ) + ch w < 0
    · rw [Finset.sum_eq_zero (fun t _ => by
          rw [if_neg (show ¬ ((t : ℤ) = (s : ℤ) + ch w) by omega), mul_zero]),
        Qf_neg _ w s hlo, zero_mul, ite_self]
    by_cases hhi : (d : ℤ) ≤ (s : ℤ) + ch w
    · rw [Finset.sum_eq_zero (fun t _ => by
        rw [if_neg (show ¬ ((t : ℤ) = (s : ℤ) + ch w) by omega), mul_zero])]
      split_ifs with h
      · have ha : chA a = -1 ∧ (s : ℤ) + ch w = d := by
          have := r.2
          obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
          all_goals simp at h ⊢; omega
        have ha0 : a = 0 := by
          obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
          all_goals simp at ha ⊢
        subst ha0
        have : ((s : ℕ) : ℚ) + (ch w : ℚ) = d := by exact_mod_cast ha.2
        rw [this]
        simp [coef]
      · rfl
    · rw [not_lt] at hlo
      rw [not_le] at hhi
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (s : ℤ) + ch w = m := ⟨_, (Int.toNat_of_nonneg hlo).symm⟩
      have hmd : m < d := by omega
      have hq : ((s : ℕ) : ℚ) + (ch w : ℚ) = m := by exact_mod_cast hm
      rw [Finset.sum_eq_single ⟨m, hmd⟩]
      · simp only [Fin.val_mk]
        rw [if_pos (show ((m : ℕ) : ℤ) = (s : ℤ) + ch w by omega), hq]
        by_cases h : (r : ℤ) = m + chA a
        · rw [if_pos h, if_pos (by omega)]; ring1
        · rw [if_neg h, if_neg (by omega), zero_mul]
      · intro t _ ht
        rw [if_neg (show ¬ ((t : ℤ) = (s : ℤ) + ch w) from fun h => ht (Fin.ext (by simp; omega))),
          mul_zero]
      · simp

lemma trace_word (d : ℕ) (w : List (Fin 3)) :
    Matrix.trace (w.map (sl2Rep d)).prod =
      if ch w = 0 then ∑ s : Fin d, Qf w ((d : ℚ) - 1) (s : ℕ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag, entry_word]
  split_ifs with h
  · exact Finset.sum_congr rfl fun s _ => by rw [if_pos (by omega)]
  · exact Finset.sum_eq_zero fun s _ => by rw [if_neg (by omega)]

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

/-- The weight system in dimension `d` is the Casimir scalar at highest weight `d - 1`. -/
theorem W_eq (d : ℕ) (hd : 1 ≤ d) : W d D = D.lam ((d : ℚ) - 1) 0 := by
  unfold W casimirWord
  rw [Matrix.trace_sum]
  have h1 : ∀ β : Fin (2 * n) → Fin 3,
      Matrix.trace (D.weight β • (List.ofFn fun i => sl2Rep d (β i)).prod) =
        ∑ s : Fin d, D.weight β * Qf (List.ofFn β) ((d : ℚ) - 1) (s : ℕ) := by
    intro β
    rw [Matrix.trace_smul, show (List.ofFn fun i => sl2Rep d (β i)) = (List.ofFn β).map (sl2Rep d)
      by rw [List.map_ofFn]; rfl, trace_word]
    by_cases hw : D.weight β = 0
    · simp [hw]
    · rw [if_pos (D.ch_ofFn_eq_zero β hw), smul_eq_mul, Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s : Fin d, ∑ β : Fin (2 * n) → Fin 3,
      D.weight β * Qf (List.ofFn β) ((d : ℚ) - 1) (s : ℕ) = D.lam ((d : ℚ) - 1) 0 := fun s => by
    rw [← D.lam_nat _ s]; rfl
  simp_rw [h2]
  rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp

theorem wsPoly_eval_W (d : ℕ) (hd : 1 ≤ d) :
    D.wsPoly.eval (((d : ℚ) ^ 2 - 1) / 8) = W d D := by
  rw [D.W_eq d hd, ← D.wsPoly_eval]
  ring_nf

end ChordDiagram

end SL2W
