import SL2W.Central

/-!
# The Verma module and the polynomial dependence on the highest weight

On the Verma module of highest weight `μ` with basis `X^j` the letters act by
`E X^j = j(μ-j+1) X^(j-1)`, `F X^j = X^(j+1)`, `H X^j = (μ-2j) X^j`. The Casimir element
of a chord diagram acts on `X^k` by a scalar `lam μ k` which does not depend on `k`.
-/

open Finset Polynomial

namespace SL2W

/-- The charge of a letter: `E` lowers the level by one and `F` raises it by one. -/
def chA : Fin 3 → ℤ := ![-1, 1, 0]

/-- The charge of a word. -/
def ch (w : List (Fin 3)) : ℤ := (w.map chA).sum

@[simp] lemma ch_nil : ch [] = 0 := rfl

lemma ch_cons (a : Fin 3) (w : List (Fin 3)) : ch (a :: w) = chA a + ch w := by
  simp [ch]

/-- The coefficient of a letter on the vector of level `j` of the Verma module of highest
weight `μ`. -/
def coef : Fin 3 → ℚ → ℚ → ℚ
  | 0, μ, j => j * (μ - j + 1)
  | 1, _, _ => 1
  | 2, μ, j => μ - 2 * j

/-- The coefficient of a word acting on the vector of level `κ`. -/
def Qf : List (Fin 3) → ℚ → ℚ → ℚ
  | [], _, _ => 1
  | a :: w, μ, κ => Qf w μ κ * coef a μ (κ + ch w)

lemma Qf_cons (a : Fin 3) (w : List (Fin 3)) (μ κ : ℚ) :
    Qf (a :: w) μ κ = Qf w μ κ * coef a μ (κ + ch w) := rfl

/-- A word whose path from level `k` goes below level `0` acts by zero. -/
lemma Qf_neg (μ : ℚ) : ∀ (w : List (Fin 3)) (k : ℕ), (k : ℤ) + ch w < 0 → Qf w μ k = 0
  | [], k, h => by simp at h; omega
  | a :: w, k, h => by
    rw [Qf_cons]
    by_cases h' : (k : ℤ) + ch w < 0
    · rw [Qf_neg μ w k h', zero_mul]
    · rw [ch_cons] at h
      have : a = 0 ∧ (k : ℤ) + ch w = 0 := by
        fin_cases a <;> simp [chA] at h ⊢ <;> omega
      obtain ⟨rfl, h0⟩ := this
      have : (k : ℚ) + ch w = 0 := by exact_mod_cast h0
      rw [this]
      simp [coef]

lemma tcoef_ne_zero {a b : Fin 3} (h : tcoef a b ≠ 0) : chA a + chA b = 0 := by
  fin_cases a <;> fin_cases b <;> simp [tcoef, chA] at h ⊢

/-! ### Operators on `ℚ[X]` -/

/-- The Verma module of highest weight `μ` realised on `ℚ[X]`. -/
noncomputable def vx (μ : ℚ) : Fin 3 → Module.End ℚ ℚ[X]
  | 0 => μ • derivative - LinearMap.mulLeft ℚ X ∘ₗ derivative ∘ₗ derivative
  | 1 => LinearMap.mulLeft ℚ X
  | 2 => μ • LinearMap.id - (2 : ℚ) • (LinearMap.mulLeft ℚ X ∘ₗ derivative)

lemma vx_rel (μ : ℚ) (a : Fin 3) :
    vx μ 1 * vx μ a - vx μ a * vx μ 1 = ∑ b, cF a b • vx μ b := by
  refine LinearMap.ext fun p => ?_
  fin_cases a <;> simp [vx, cF, Fin.sum_univ_three, derivative_mul, smul_eq_C_mul, map_ofNat] <;>
    ring

lemma X_mul_derivative (q : ℚ) (m : ℕ) : X * derivative (C q * X ^ m) = C (q * m) * X ^ m := by
  cases m with
  | zero => simp
  | succ m => rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, ← mul_assoc, mul_comm X, mul_assoc,
      ← pow_succ']

lemma vx_F (μ q : ℚ) (m : ℕ) : vx μ 1 (C q * X ^ m) = C q * X ^ (m + 1) := by
  simp [vx, pow_succ]; ring

lemma vx_H (μ q : ℚ) (m : ℕ) : vx μ 2 (C q * X ^ m) = C (q * (μ - 2 * m)) * X ^ m := by
  have h : vx μ 2 (C q * X ^ m) = μ • (C q * X ^ m) - (2 : ℚ) • (X * derivative (C q * X ^ m)) := rfl
  rw [h, X_mul_derivative]
  simp only [smul_eq_C_mul, map_mul, map_sub, map_natCast, map_ofNat]
  ring

lemma vx_E (μ q : ℚ) (m : ℕ) :
    vx μ 0 (C q * X ^ (m + 1)) = C (q * ((m + 1) * (μ - m))) * X ^ m := by
  have h : vx μ 0 (C q * X ^ (m + 1)) = μ • derivative (C q * X ^ (m + 1)) -
      X * derivative (derivative (C q * X ^ (m + 1))) := rfl
  have d1 : derivative (C q * X ^ (m + 1)) = C (q * (m + 1)) * X ^ m := by
    rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]; push_cast; rfl
  rw [h, d1, X_mul_derivative]
  simp only [smul_eq_C_mul, map_mul, map_sub, map_natCast, map_add, map_one]
  ring

lemma vx_E_zero (μ q : ℚ) : vx μ 0 (C q) = 0 := by
  simp [vx]

/-- A word acts on `X^k` by `Qf` followed by a shift of the level by the charge. -/
lemma word_act (μ : ℚ) : ∀ (w : List (Fin 3)) (k : ℕ),
    (w.map (vx μ)).prod (X ^ k) = C (Qf w μ k) * X ^ ((k : ℤ) + ch w).toNat
  | [], k => by simp [Qf]
  | a :: w, k => by
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, word_act μ w k, Qf_cons]
    by_cases hneg : (k : ℤ) + ch w < 0
    · rw [Qf_neg μ w k hneg]
      simp
    · rw [not_lt] at hneg
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (k : ℤ) + ch w = m := ⟨_, (Int.toNat_of_nonneg hneg).symm⟩
      have hq : (k : ℚ) + ch w = m := by exact_mod_cast hm
      rw [hm, Int.toNat_natCast, hq, ch_cons, show (k : ℤ) + (chA a + ch w) = chA a + m by omega]
      obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
      · cases m with
        | zero => simp [vx_E_zero, coef]
        | succ m =>
          rw [vx_E]
          simp only [chA, Fin.zero_eta, Matrix.cons_val_zero]
          rw [show (-1 : ℤ) + ((m + 1 : ℕ) : ℤ) = (m : ℤ) by push_cast; ring, Int.toNat_natCast]
          simp only [coef]
          push_cast
          ring_nf
      · rw [vx_F]
        simp only [chA, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [show (1 : ℤ) + (m : ℤ) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
        simp [coef]
      · rw [vx_H]
        simp only [chA]
        simp [coef]

/-! ### Polynomial dependence on the level and on the highest weight -/

/-- The coefficient of a letter as a polynomial in the level. -/
noncomputable def coefP : Fin 3 → ℚ → ℚ[X]
  | 0, μ => X * (C (μ + 1) - X)
  | 1, _ => 1
  | 2, μ => C μ - 2 * X

lemma coefP_eval (a : Fin 3) (μ t : ℚ) : (coefP a μ).eval t = coef a μ t := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp only [coefP, coef, eval_mul, eval_X, eval_sub, eval_C]; ring
  · simp [coefP, coef]
  · simp [coefP, coef]

/-- `Qf` as a polynomial in the level. -/
noncomputable def QK : List (Fin 3) → ℚ → ℚ[X]
  | [], _ => 1
  | a :: w, μ => QK w μ * (coefP a μ).comp (X + C (ch w : ℚ))

lemma QK_eval (μ κ : ℚ) : ∀ w : List (Fin 3), (QK w μ).eval κ = Qf w μ κ
  | [] => by simp [QK, Qf]
  | a :: w => by simp [QK, Qf_cons, QK_eval μ κ w, eval_comp, coefP_eval]

/-- The coefficient of a letter on level `t` as a polynomial in the highest weight. -/
noncomputable def coefM : Fin 3 → ℚ → ℚ[X]
  | 0, t => C t * (X - C t + 1)
  | 1, _ => 1
  | 2, t => X - C (2 * t)

lemma coefM_eval (a : Fin 3) (μ t : ℚ) : (coefM a t).eval μ = coef a μ t := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp [coefM, coef]
  · simp [coefM, coef]
  · simp [coefM, coef]

/-- `Qf` at level `0` as a polynomial in the highest weight. -/
noncomputable def QM : List (Fin 3) → ℚ[X]
  | [] => 1
  | a :: w => QM w * coefM a (ch w)

lemma QM_eval (μ : ℚ) : ∀ w : List (Fin 3), (QM w).eval μ = Qf w μ 0
  | [] => by simp [QM, Qf]
  | a :: w => by simp [QM, Qf_cons, QM_eval μ w, coefM_eval]

lemma coef_symm (a : Fin 3) (μ t : ℚ) : coef a μ (t + μ + 1) = coef a (-2 - μ) t := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp [coef]; ring
  · simp [coef]
  · simp [coef]; ring

lemma Qf_symm (μ κ : ℚ) : ∀ w : List (Fin 3), Qf w μ (κ + μ + 1) = Qf w (-2 - μ) κ
  | [] => rfl
  | a :: w => by
    rw [Qf_cons, Qf_cons, Qf_symm μ κ w, show κ + μ + 1 + ch w = (κ + ch w) + μ + 1 by ring,
      coef_symm]

lemma coeff_comp_neg_X (p : ℚ[X]) (k : ℕ) : (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow,
      show ((-1 : ℚ[X]) ^ m) = C ((-1) ^ m) by simp, ← mul_assoc, ← map_mul, coeff_C_mul,
      coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma ch_ofFn (β : Fin (2 * n) → Fin 3) : ch (List.ofFn β) = ∑ i, chA (β i) := by
  simp [ch, List.map_ofFn, List.sum_ofFn]

lemma ch_ofFn_eq_zero (β : Fin (2 * n) → Fin 3) (h : D.weight β ≠ 0) : ch (List.ofFn β) = 0 := by
  rw [ch_ofFn, D.sum_pairs]
  apply Finset.sum_eq_zero
  intro c _
  rw [D.weight_eq] at h
  exact tcoef_ne_zero (Finset.prod_ne_zero_iff.mp h c (mem_univ _))

/-- The scalar by which the Casimir element acts on the vector of level `κ` of the Verma
module of highest weight `μ`. -/
def lam (μ κ : ℚ) : ℚ := ∑ β : Fin (2 * n) → Fin 3, D.weight β * Qf (List.ofFn β) μ κ

lemma casimir_act (μ : ℚ) (k : ℕ) : D.casimirWord (vx μ) (X ^ k) = C (D.lam μ k) * X ^ k := by
  unfold casimirWord lam
  rw [LinearMap.sum_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β _
  rw [LinearMap.smul_apply, show (List.ofFn fun i => vx μ (β i)) = (List.ofFn β).map (vx μ) by
    rw [List.map_ofFn]; rfl, word_act]
  by_cases hw : D.weight β = 0
  · simp [hw]
  · rw [D.ch_ofFn_eq_zero β hw, add_zero, Int.toNat_natCast, smul_eq_C_mul, ← mul_assoc,
      ← map_mul]

lemma lam_succ (μ : ℚ) (k : ℕ) : D.lam μ (k + 1) = D.lam μ k := by
  have h := congrArg (fun f : Module.End ℚ ℚ[X] => f (X ^ k)) (D.casimir_comm (vx μ) (vx_rel μ))
  simp only [Module.End.mul_apply] at h
  have hF : vx μ 1 (X ^ k) = X ^ (k + 1) := by simpa using vx_F μ 1 k
  rw [casimir_act, hF, casimir_act, vx_F] at h
  have := congrArg (fun p => coeff p (k + 1)) h
  simp only [coeff_C_mul, coeff_X_pow_self, mul_one] at this
  rw [show ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) by push_cast; ring]
  exact this.symm

lemma lam_nat (μ : ℚ) (k : ℕ) : D.lam μ k = D.lam μ 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, D.lam_succ, ih]

lemma infinite_nat_cast : Set.Infinite (Set.range (Nat.cast : ℕ → ℚ)) :=
  Set.infinite_range_of_injective Nat.cast_injective

/-- `lam` as a polynomial in the level. -/
noncomputable def lamK (μ : ℚ) : ℚ[X] :=
  ∑ β : Fin (2 * n) → Fin 3, C (D.weight β) * QK (List.ofFn β) μ

lemma lamK_eval (μ κ : ℚ) : (D.lamK μ).eval κ = D.lam μ κ := by
  simp [lamK, lam, eval_finset_sum, QK_eval]

/-- The Casimir scalar does not depend on the level. -/
lemma lam_const (μ κ : ℚ) : D.lam μ κ = D.lam μ 0 := by
  have h : D.lamK μ = C (D.lam μ 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine infinite_nat_cast.mono ?_
    rintro _ ⟨k, rfl⟩
    simp [lamK_eval, D.lam_nat]
  rw [← D.lamK_eval, h, eval_C]

lemma lam_symm (μ : ℚ) : D.lam μ 0 = D.lam (-2 - μ) 0 := by
  rw [← D.lam_const μ (0 + μ + 1)]
  unfold lam
  simp_rw [Qf_symm]

/-- `lam μ 0` as a polynomial in `μ`. -/
noncomputable def lamM : ℚ[X] := ∑ β : Fin (2 * n) → Fin 3, C (D.weight β) * QM (List.ofFn β)

lemma lamM_eval (μ : ℚ) : D.lamM.eval μ = D.lam μ 0 := by
  simp [lamM, lam, eval_finset_sum, QM_eval]

/-- The polynomial `lamM` recentred at `-1`; it is even. -/
noncomputable def gP : ℚ[X] := D.lamM.comp (X - 1)

lemma gP_eval (y : ℚ) : D.gP.eval y = D.lam (y - 1) 0 := by
  simp [gP, eval_comp, lamM_eval]

lemma gP_even : D.gP.comp (-X) = D.gP := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_univ.mono ?_
  intro y _
  simp only [Set.mem_setOf_eq, eval_comp, eval_neg, eval_X, gP_eval]
  rw [D.lam_symm (-y - 1)]
  ring_nf

lemma gP_coeff_odd (k : ℕ) (hk : ¬ 2 ∣ k) : D.gP.coeff k = 0 := by
  have h := congrArg (fun p => coeff p k) D.gP_even
  simp only [coeff_comp_neg_X] at h
  rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))] at h
  linarith

lemma expand_contract_gP : expand ℚ 2 (contract 2 D.gP) = D.gP := by
  ext k
  rw [coeff_expand (by norm_num)]
  split_ifs with h
  · rw [coeff_contract two_ne_zero, Nat.div_mul_cancel h]
  · rw [D.gP_coeff_odd k h]

/-- The polynomial in `c = (d² - 1)/8` interpolating the weight system. -/
noncomputable def wsPoly : ℚ[X] := (contract 2 D.gP).comp (8 * X + 1)

lemma wsPoly_eval (μ : ℚ) : D.wsPoly.eval (((μ + 1) ^ 2 - 1) / 8) = D.lam μ 0 := by
  rw [wsPoly, eval_comp]
  simp only [eval_add, eval_mul, eval_X, eval_one, eval_ofNat]
  rw [show (8 : ℚ) * (((μ + 1) ^ 2 - 1) / 8) + 1 = (μ + 1) ^ 2 by ring, ← expand_eval,
    expand_contract_gP, gP_eval, add_sub_cancel_right]

end ChordDiagram

end SL2W
