import SL2W.Words

/-!
# The bosonic twisted trace on words in `z` and `∂`

A word is a list of letters `0 = z`, `1 = ∂`, read as an operator on `ℚ[z]` with the last
letter acting first. A word sends `z^k` to `(Pw w).eval k • z^(k + chg w)`. The functional
`τb` is a twisted trace: it satisfies the canonical commutation relation, the twisted
cyclicity `τb (a :: w) = -τb (w ++ [a])` and hence the Wick rule.
-/

open Polynomial

namespace SL2W

/-- The charge of a word: the number of `z` minus the number of `∂`. -/
def chg : List (Fin 2) → ℤ
  | [] => 0
  | a :: w => chg w + (if a = 0 then 1 else -1)

@[simp] lemma chg_nil : chg [] = 0 := rfl
@[simp] lemma chg_cons (a : Fin 2) (w : List (Fin 2)) :
    chg (a :: w) = chg w + (if a = 0 then 1 else -1) := rfl

lemma chg_append (A w : List (Fin 2)) : chg (A ++ w) = chg A + chg w := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih]; ring

/-- The coefficient polynomial of a word. -/
noncomputable def Pw : List (Fin 2) → ℚ[X]
  | [] => 1
  | a :: w => if a = 0 then Pw w else Pw w * (X + C (chg w : ℚ))

@[simp] lemma Pw_nil : Pw [] = 1 := rfl
@[simp] lemma Pw_cons (a : Fin 2) (w : List (Fin 2)) :
    Pw (a :: w) = if a = 0 then Pw w else Pw w * (X + C (chg w : ℚ)) := rfl

/-- The factor contributed by a prefix acting on a state of charge `c`. -/
noncomputable def Rw : List (Fin 2) → ℤ → ℚ[X]
  | [], _ => 1
  | a :: A, c => if a = 0 then Rw A c else Rw A c * (X + C ((c + chg A : ℤ) : ℚ))

lemma Pw_append (A w : List (Fin 2)) : Pw (A ++ w) = Pw w * Rw A (chg w) := by
  induction A with
  | nil => simp [Rw]
  | cons a A ih =>
    simp only [List.cons_append, Pw_cons, Rw, ih, chg_append]
    split_ifs
    · rfl
    · push_cast; ring

lemma Rw_shift (A : List (Fin 2)) (c : ℤ) : Rw A (c + 1) = (Rw A c).comp (X + 1) := by
  induction A with
  | nil => simp [Rw]
  | cons a A ih =>
    simp only [Rw]
    split_ifs
    · exact ih
    · rw [ih, mul_comp, add_comp, X_comp, C_comp]
      push_cast
      simp only [map_add, map_one]
      ring

lemma Pw_eval_neg (w : List (Fin 2)) (k : ℕ) (h : (k : ℤ) + chg w < 0) :
    (Pw w).eval (k : ℚ) = 0 := by
  induction w with
  | nil => simp at h; omega
  | cons a w ih =>
    simp only [Pw_cons]
    split_ifs with ha
    · apply ih; simp [ha] at h; omega
    · simp only [chg_cons, ha, if_false] at h
      rw [eval_mul]
      by_cases h' : (k : ℤ) + chg w < 0
      · rw [ih h', zero_mul]
      · have : (k : ℤ) + chg w = 0 := by omega
        have : (k : ℚ) + (chg w : ℚ) = 0 := by exact_mod_cast this
        simp [this]

/-- The diagonal part of a word. -/
noncomputable def Pdiag (w : List (Fin 2)) : ℚ[X] := if chg w = 0 then Pw w else 0

lemma Pw_comm (A B : List (Fin 2)) :
    Pw (A ++ 1 :: 0 :: B) = Pw (A ++ 0 :: 1 :: B) + Pw (A ++ B) := by
  rw [Pw_append, Pw_append, Pw_append]
  simp only [chg_cons, Pw_cons, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    if_false]
  norm_num
  push_cast
  ring

lemma Pdiag_comm (A B : List (Fin 2)) :
    Pdiag (A ++ 1 :: 0 :: B) = Pdiag (A ++ 0 :: 1 :: B) + Pdiag (A ++ B) := by
  have h1 : chg (A ++ 1 :: 0 :: B) = chg (A ++ B) := by simp [chg_append]
  have h2 : chg (A ++ 0 :: 1 :: B) = chg (A ++ B) := by simp [chg_append]
  unfold Pdiag
  rw [h1, h2]
  split_ifs
  · exact Pw_comm A B
  · simp

/-- The coefficients of the even Euler-type functional. -/
noncomputable def eS : ℕ → ℚ
  | 0 => 1
  | n + 1 => -(1 / 2) * ∑ i : Fin (n + 1), ((n + 1).choose i : ℚ) * eS i
decreasing_by exact i.isLt

lemma eS_succ (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ((n + 1).choose i : ℚ) * eS i = -2 * eS (n + 1) := by
  rw [eS, ← Fin.sum_univ_eq_sum_range (fun i => ((n + 1).choose i : ℚ) * eS i)]
  ring

/-- The twisted functional on polynomials. -/
noncomputable def ell : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun i => eS i • LinearMap.id

lemma ell_monomial (n : ℕ) (a : ℚ) : ell (monomial n a) = eS n * a := by
  simp [ell, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

lemma ell_C (a : ℚ) : ell (C a) = a := by
  rw [← monomial_zero_left, ell_monomial]; simp [eS]

lemma X_add_one_pow (n : ℕ) :
    (X + 1 : ℚ[X]) ^ n = ∑ i ∈ Finset.range (n + 1), monomial i (n.choose i : ℚ) := by
  ext k
  rw [coeff_X_add_one_pow, finset_sum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

lemma ell_shift (p : ℚ[X]) : ell p + ell (p.comp (X + 1)) = 2 * p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, map_add, map_add, eval_add]
    linarith
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, X_add_one_pow,
      Finset.mul_sum, map_sum, C_mul_X_pow_eq_monomial, ell_monomial]
    simp only [C_mul_monomial, ell_monomial, eval_monomial]
    cases n with
    | zero => simp [eS]; ring
    | succ n =>
      rw [Finset.sum_range_succ]
      have h := eS_succ n
      have : ∑ x ∈ Finset.range (n + 1), eS x * (a * ((n + 1).choose x : ℚ)) =
          a * ∑ i ∈ Finset.range (n + 1), ((n + 1).choose i : ℚ) * eS i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this, h]
      simp
      ring

/-- The bosonic twisted trace of a word. -/
noncomputable def τb (w : List (Fin 2)) : ℚ := ell (Pdiag w)

/-- The commutator `[a, b]` of two letters, as a scalar: `[∂, z] = 1`. -/
def ω (a b : Fin 2) : ℚ := if a = 1 ∧ b = 0 then 1 else if a = 0 ∧ b = 1 then -1 else 0

lemma τb_comm (A B : List (Fin 2)) (a b : Fin 2) :
    τb (A ++ a :: b :: B) = τb (A ++ b :: a :: B) + ω a b * τb (A ++ B) := by
  unfold τb
  fin_cases a <;> fin_cases b <;> simp [ω]
  · rw [Pdiag_comm, map_add]; ring
  · rw [Pdiag_comm, map_add]

lemma τb_cyc_z (w : List (Fin 2)) : τb (0 :: w) = -τb (w ++ [0]) := by
  unfold τb Pdiag
  have hw : Pw w = Rw w 0 := by simpa using Pw_append w []
  have e1 : Pw (w ++ [0]) = Rw w 1 := by rw [Pw_append]; simp
  have e2 : chg (w ++ [0]) = chg w + 1 := by rw [chg_append]; simp
  have e3 : chg (0 :: w) = chg w + 1 := by simp
  have e4 : Pw (0 :: w) = Pw w := by simp
  rw [e1, e2, e3, e4]
  by_cases h : chg w + 1 = 0
  · rw [if_pos h, if_pos h]
    have hs := ell_shift (Pw w)
    rw [hw, ← Rw_shift] at hs
    have h0 : (Rw w 0).eval 0 = 0 := by
      rw [← hw]; exact_mod_cast Pw_eval_neg w 0 (by simp; omega)
    rw [h0, zero_add] at hs
    rw [hw]
    linarith
  · rw [if_neg h, if_neg h]; simp

lemma τb_cyc_d (w : List (Fin 2)) : τb (1 :: w) = -τb (w ++ [1]) := by
  unfold τb Pdiag
  have hw : Pw w = Rw w 0 := by simpa using Pw_append w []
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have e1 : Pw (w ++ [1]) = X * Rw w (-1) := by rw [Pw_append]; simp [h10]
  have e2 : chg (w ++ [1]) = chg w - 1 := by rw [chg_append]; simp [h10]; ring
  have e3 : chg (1 :: w) = chg w - 1 := by simp [h10]; ring
  have e4 : Pw (1 :: w) = Pw w * (X + C (chg w : ℚ)) := by simp [h10]
  rw [e1, e2, e3, e4]
  by_cases h : chg w - 1 = 0
  · rw [if_pos h, if_pos h]
    have hs := ell_shift (X * Rw w (-1))
    have hc : chg w = (-1 : ℤ) + 1 + 1 := by omega
    have e : (X * Rw w (-1)).comp (X + 1) = Pw w * (X + C (chg w : ℚ)) := by
      rw [hw, show (0 : ℤ) = -1 + 1 by norm_num, Rw_shift, mul_comp, X_comp, hc]
      norm_num
      ring
    rw [e, eval_mul, eval_X, zero_mul, mul_zero] at hs
    linarith
  · rw [if_neg h, if_neg h]; simp

lemma τb_cyc (a : Fin 2) (w : List (Fin 2)) : τb (a :: w) = -τb (w ++ [a]) := by
  fin_cases a
  · exact τb_cyc_z w
  · exact τb_cyc_d w

lemma τb_move (A B : List (Fin 2)) (a : Fin 2) :
    τb (A ++ a :: B) = τb (A ++ B ++ [a]) +
      ((splits B).map fun s => ω a s.2.1 * τb (A ++ s.1 ++ s.2.2)).sum := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih =>
    rw [τb_comm, show A ++ b :: a :: B = (A ++ [b]) ++ a :: B by simp, ih]
    simp only [splits_cons, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.append_assoc, List.singleton_append, List.nil_append, Function.comp_def,
      List.cons_append]
    ring

/-- The Wick rule for the twisted trace. -/
lemma τb_wick (a : Fin 2) (w : List (Fin 2)) :
    τb (a :: w) = (1 / 2) * ((splits w).map fun s => ω a s.2.1 * τb (s.1 ++ s.2.2)).sum := by
  have h := τb_move [] w a
  simp only [List.nil_append] at h
  rw [τb_cyc a w] at h ⊢
  linarith

end SL2W
