import SL2W.Trace
import SL2W.Legs

/-!
# The oscillator representation at highest weight `-1/2`

The letters act on `ℚ[z]` by `F = z²`, `E = -¼ ∂²`, `H = -½ (z∂ + ∂z)`. On even powers of `z`
this is the Verma module of highest weight `-1/2`, so the Casimir element of a chord diagram
acts by `lam (-1/2) 0`. Expanding every letter in the bosonic letters `z, ∂` and summing over
the letters of the chords gives `ξ` of the intersection graph.
-/

open Finset Polynomial

namespace SL2W

/-- The coefficients of the letters `E, F, H` in the words `zz, z∂, ∂z, ∂∂`. -/
def Qa (a : Fin 3) (x : Fin 2 × Fin 2) : ℚ :=
  if a = 0 ∧ x = (1, 1) then -1 / 4
  else if a = 1 ∧ x = (0, 0) then 1
  else if a = 2 ∧ (x = (0, 1) ∨ x = (1, 0)) then -1 / 2
  else 0

/-- The factor by which a letter multiplies the coefficient, as a polynomial in the degree. -/
noncomputable def gA : Fin 3 → ℚ[X]
  | 0 => C (-1 / 4) * (X * (X - 1))
  | 1 => 1
  | 2 => C (-1 / 2) * (2 * X + 1)

lemma gA_eval (a : Fin 3) (t : ℚ) : (gA a).eval (2 * t) = coef a (-1 / 2) t := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp only [gA, coef, eval_mul, eval_C, eval_X, eval_sub, eval_one]; ring
  · simp [gA, coef]
  · simp only [gA, coef, eval_mul, eval_add, eval_X, eval_C, eval_one, eval_ofNat]; ring

/-- The coefficient polynomial of a word in the oscillator representation. -/
noncomputable def OscP : List (Fin 3) → ℚ[X]
  | [] => 1
  | a :: w => OscP w * (gA a).comp (X + C (2 * (ch w : ℚ)))

lemma OscP_eval (κ : ℚ) : ∀ w : List (Fin 3), (OscP w).eval (2 * κ) = Qf w (-1 / 2) κ
  | [] => by simp [OscP, Qf]
  | a :: w => by
    rw [OscP, Qf_cons, eval_mul, OscP_eval κ w, eval_comp, ← gA_eval]
    simp only [eval_add, eval_X, eval_C]
    ring_nf

/-- The factor of a pair of bosonic letters acting on a state of charge `c`. -/
noncomputable def bf (x : Fin 2 × Fin 2) (c : ℤ) : ℚ[X] :=
  (if x.2 = 0 then 1 else X + C (c : ℚ)) *
    (if x.1 = 0 then 1 else X + C (((c + if x.2 = 0 then 1 else -1 : ℤ)) : ℚ))

lemma Pw_pair (x : Fin 2 × Fin 2) (W : List (Fin 2)) :
    Pw (x.1 :: x.2 :: W) = Pw W * bf x (chg W) := by
  simp only [Pw_cons, chg_cons, bf]
  split_ifs <;> ring

lemma letter_expand (a : Fin 3) (c : ℤ) :
    ∑ x : Fin 2 × Fin 2, C (Qa a x) * bf x c = (gA a).comp (X + C (c : ℚ)) := by
  rw [Fintype.sum_prod_type]
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp [Fin.sum_univ_two, Qa, bf]
    simp only [gA, mul_comp, C_comp, X_comp, sub_comp, one_comp]
    ring
  · simp [Fin.sum_univ_two, Qa, bf, gA]
  · simp [Fin.sum_univ_two, Qa, bf]
    simp only [gA, mul_comp, C_comp, X_comp, add_comp, one_comp, ofNat_comp]
    ring

lemma flat_cons {m : ℕ} (x : Fin 2 × Fin 2) (h : Fin m → Fin 2 × Fin 2) :
    flat (Fin.cons x h : Fin (m + 1) → Fin 2 × Fin 2) = x.1 :: x.2 :: flat h := by
  simp [flat, List.ofFn_succ]

lemma Qa_ne_zero {a : Fin 3} {x : Fin 2 × Fin 2} (h : Qa a x ≠ 0) :
    (if x.1 = 0 then (1 : ℤ) else -1) + (if x.2 = 0 then 1 else -1) = 2 * chA a := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  all_goals
    obtain ⟨x1, x2⟩ := x
    fin_cases x1 <;> fin_cases x2 <;> simp [Qa] at h ⊢

lemma chg_flat : ∀ (m : ℕ) (y : Fin m → Fin 3) (h : Fin m → Fin 2 × Fin 2),
    (∏ i, Qa (y i) (h i)) ≠ 0 → chg (flat h) = 2 * ch (List.ofFn y)
  | 0, y, h, _ => by simp [flat]
  | m + 1, y, h, hq => by
    rw [Fin.prod_univ_succ] at hq
    have h1 : Qa (y 0) (h 0) ≠ 0 := left_ne_zero_of_mul hq
    have h2 := right_ne_zero_of_mul hq
    rw [← Fin.cons_self_tail h, flat_cons, List.ofFn_succ, ch_cons]
    simp only [chg_cons]
    rw [chg_flat m (fun i => y i.succ) (Fin.tail h) h2]
    have := Qa_ne_zero h1
    linarith

/-- Expansion of an oscillator word into bosonic words. -/
lemma OscP_expand : ∀ (m : ℕ) (y : Fin m → Fin 3),
    OscP (List.ofFn y) = ∑ h : Fin m → Fin 2 × Fin 2, C (∏ i, Qa (y i) (h i)) * Pw (flat h)
  | 0, y => by simp [OscP, flat]
  | m + 1, y => by
    rw [List.ofFn_succ, OscP, OscP_expand m, sum_fin_succ_fun, Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h' _
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, flat_cons, Pw_pair]
    by_cases hq : (∏ i : Fin m, Qa (y i.succ) (h' i)) = 0
    · simp [hq]
    · rw [chg_flat m _ h' hq, show (2 : ℚ) * (ch (List.ofFn fun i => y i.succ) : ℚ) =
        ((2 * ch (List.ofFn fun i => y i.succ) : ℤ) : ℚ) by push_cast; ring, ← letter_expand,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [map_mul]
      ring

lemma ell_C_mul (a : ℚ) (p : ℚ[X]) : ell (C a * p) = a * ell p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- The kernel of a chord in the bosonic letters. -/
def Kc (x y : Fin 2 × Fin 2) : ℚ := ∑ a, ∑ b, tcoef a b * Qa a x * Qa b y

lemma Kc_eq (x y : Fin 2 × Fin 2) : Kc x y = -1 / 32 * (pairK 0 x y + pairK 1 x y) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    simp [Kc, Qa, tcoef, pairK, pairW, ω, Fin.sum_univ_three] <;> norm_num

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma prod_pairs {M : Type*} [CommMonoid M] (f : Fin (2 * n) → M) :
    ∏ i, f i = ∏ c : D.Chord, (f c.1 * f (D.σ c.1)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => i < D.σ i), Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_subtype _ (fun i => by simp) f
  · apply Finset.prod_nbij' (fun p => D.chordOf p) (fun c => D.σ c.1)
    · intro p _; exact mem_univ _
    · intro c _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [D.invol]; exact not_lt.mpr c.2.le
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [D.chordOf_val, if_neg hp, D.invol]
    · intro c _; exact D.chordOf_σ c
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [D.chordOf_val, if_neg hp, D.invol]

/-- Labellings of the endpoints are labellings of the chords by ordered pairs. -/
def endsEquiv (γ : Type*) : (Fin (2 * n) → γ) ≃ (D.Chord → γ × γ) where
  toFun β c := (β c.1, β (D.σ c.1))
  invFun κ p := if p < D.σ p then (κ (D.chordOf p)).1 else (κ (D.chordOf p)).2
  left_inv β := by
    funext p
    by_cases hp : p < D.σ p
    · simp only [if_pos hp]
      congr 1
      rw [D.chordOf_val, if_pos hp]
    · simp only [if_neg hp]
      congr 1
      rw [D.chordOf_val, if_neg hp, D.invol]
  right_inv κ := by
    funext c
    have h1 : ¬ D.σ c.1 < D.σ (D.σ c.1) := by rw [D.invol]; exact not_lt.mpr c.2.le
    simp only [if_pos c.2, if_neg h1, D.chordOf_self, D.chordOf_σ]

lemma sum_weight_Qa (h : Fin (2 * n) → Fin 2 × Fin 2) :
    ∑ β : Fin (2 * n) → Fin 3, D.weight β * ∏ i, Qa (β i) (h i) =
      ∏ c : D.Chord, Kc (h c.1) (h (D.σ c.1)) := by
  have e : ∀ β : Fin (2 * n) → Fin 3, D.weight β * ∏ i, Qa (β i) (h i) =
      ∏ c : D.Chord, (tcoef (D.endsEquiv _ β c).1 (D.endsEquiv _ β c).2 *
        Qa (D.endsEquiv _ β c).1 (h c.1) * Qa (D.endsEquiv _ β c).2 (h (D.σ c.1))) := by
    intro β
    rw [D.weight_eq, D.prod_pairs, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c _
    simp only [endsEquiv, Equiv.coe_fn_mk]
    ring
  simp_rw [e]
  rw [Fintype.sum_equiv (D.endsEquiv (Fin 3)) _
    (fun κ => ∏ c : D.Chord, (tcoef (κ c).1 (κ c).2 * Qa (κ c).1 (h c.1) * Qa (κ c).2 (h (D.σ c.1))))
    (fun β => rfl)]
  rw [← Fintype.prod_sum (fun (c : D.Chord) (p : Fin 3 × Fin 3) =>
    tcoef p.1 p.2 * Qa p.1 (h c.1) * Qa p.2 (h (D.σ c.1)))]
  apply Finset.prod_congr rfl
  intro c _
  rw [Kc, ← Fintype.sum_prod_type']

/-- The polynomial of the Casimir element in the oscillator representation. -/
noncomputable def Rosc : ℚ[X] := ∑ β : Fin (2 * n) → Fin 3, C (D.weight β) * OscP (List.ofFn β)

lemma Rosc_eq : D.Rosc = C (D.lam (-1 / 2) 0) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_univ.mono ?_
  intro y _
  simp only [Set.mem_setOf_eq, Rosc, eval_finset_sum, eval_mul, eval_C]
  rw [show y = 2 * (y / 2) by ring]
  simp_rw [OscP_eval]
  rw [← D.lam_const (-1 / 2) (y / 2)]
  rfl

lemma ell_Rosc : ell D.Rosc = ∑ h : Fin (2 * n) → Fin 2 × Fin 2,
    (∏ c : D.Chord, Kc (h c.1) (h (D.σ c.1))) * τb (flat h) := by
  unfold Rosc
  simp_rw [OscP_expand, Finset.mul_sum, map_sum, ← mul_assoc, ← map_mul, ell_C_mul]
  have e : ∀ (β : Fin (2 * n) → Fin 3) (h : Fin (2 * n) → Fin 2 × Fin 2),
      D.weight β * (∏ i, Qa (β i) (h i)) * ell (Pw (flat h)) =
        D.weight β * (∏ i, Qa (β i) (h i)) * τb (flat h) := by
    intro β h
    by_cases hz : D.weight β * (∏ i, Qa (β i) (h i)) = 0
    · rw [hz, zero_mul, zero_mul]
    · have hw : D.weight β ≠ 0 := left_ne_zero_of_mul hz
      have hq := right_ne_zero_of_mul hz
      have hc : chg (flat h) = 0 := by
        rw [chg_flat _ β h hq, D.ch_ofFn_eq_zero β hw, mul_zero]
      rw [τb, Pdiag, if_pos hc]
  simp_rw [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_mul, D.sum_weight_Qa]

/-- The Casimir scalar at highest weight `-1/2` is `ξ` of the intersection graph. -/
theorem lam_half : D.lam (-1 / 2) 0 = ξ D.interGraph := by
  have h1 : ell D.Rosc = D.lam (-1 / 2) 0 := by rw [D.Rosc_eq, ell_C]
  rw [← h1, D.ell_Rosc]
  have h2 : ∀ h : Fin (2 * n) → Fin 2 × Fin 2,
      (∏ c : D.Chord, Kc (h c.1) (h (D.σ c.1))) * τb (flat h) =
        (-1 / 32 : ℚ) ^ n * ∑ β' : D.Chord → Fin 2,
          (∏ c, pairK (β' c) (h c.1) (h (D.σ c.1))) * τb (flat h) := by
    intro h
    simp_rw [Kc_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, D.card_chord, ← Finset.sum_mul,
      ← mul_assoc]
    congr 2
    rw [← Fintype.prod_sum (fun (c : D.Chord) (b : Fin 2) => pairK b (h c.1) (h (D.σ c.1)))]
    apply Finset.prod_congr rfl
    intro c _
    rw [Fin.sum_univ_two]
  simp_rw [h2]
  rw [← Finset.mul_sum, Finset.sum_comm, D.boson_graph, ← mul_assoc, ← mul_pow]
  norm_num

end ChordDiagram

end SL2W
