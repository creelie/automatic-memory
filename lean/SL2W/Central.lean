import SL2W.Colour

/-!
# The Casimir element of a chord diagram commutes with `F`

In any `ℚ`-algebra with elements `E, F, H` such that `[F, E] = -H` and `[F, H] = 2F`, the
element obtained by placing the Casimir tensor on every chord commutes with `F`.
-/

open Finset

namespace SL2W

section Update

variable {A : Type*} [Ring A] [Algebra ℚ A]

omit [Ring A] [Algebra ℚ A] in
lemma ofFn_update_zero {m : ℕ} (y : Fin (m + 1) → A) (v : A) :
    List.ofFn (Function.update y 0 v) = v :: List.ofFn (fun j => y j.succ) := by
  rw [List.ofFn_succ, Function.update_self]
  congr 1

omit [Ring A] [Algebra ℚ A] in
lemma ofFn_update_succ {m : ℕ} (y : Fin (m + 1) → A) (i : Fin m) (v : A) :
    List.ofFn (Function.update y i.succ v) =
      y 0 :: List.ofFn (Function.update (fun j => y j.succ) i v) := by
  rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  congr 1
  apply congrArg
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Fin.succ_injective _ e))]

omit [Algebra ℚ A] in
lemma comm_prod_ofFn (x : A) : ∀ (m : ℕ) (y : Fin m → A),
    x * (List.ofFn y).prod - (List.ofFn y).prod * x =
      ∑ i, (List.ofFn (Function.update y i (x * y i - y i * x))).prod
  | 0, y => by simp
  | m + 1, y => by
    rw [Fin.sum_univ_succ, ofFn_update_zero]
    simp only [ofFn_update_succ, List.prod_cons]
    rw [List.ofFn_succ]
    simp only [List.prod_cons]
    have ih := comm_prod_ofFn x m (fun j => y j.succ)
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

lemma prod_update_sum {ι : Type*} (s : Finset ι) (c : ι → ℚ) (z : ι → A) :
    ∀ (m : ℕ) (y : Fin m → A) (i : Fin m),
      (List.ofFn (Function.update y i (∑ b ∈ s, c b • z b))).prod =
        ∑ b ∈ s, c b • (List.ofFn (Function.update y i (z b))).prod
  | 0, _, i => i.elim0
  | m + 1, y, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ofFn_update_zero, List.prod_cons, Finset.sum_mul, smul_mul_assoc]
    · simp only [ofFn_update_succ, List.prod_cons]
      rw [prod_update_sum s c z m _ i, Finset.mul_sum]
      simp only [mul_smul_comm]

end Update

/-- The structure constants of `ad F` in the basis `E, F, H`: `[F, E] = -H`, `[F, H] = 2F`. -/
def cF (a b : Fin 3) : ℚ := if a = 0 ∧ b = 2 then -1 else if a = 2 ∧ b = 1 then 2 else 0

lemma tcoef_invariant (u v : Fin 3) :
    ∑ a, tcoef a v * cF a u + ∑ a, tcoef u a * cF a v = 0 := by
  fin_cases u <;> fin_cases v <;> simp [Fin.sum_univ_three, tcoef, cF] <;> norm_num

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma weight_eq (β : Fin (2 * n) → Fin 3) :
    D.weight β = ∏ c : D.Chord, tcoef (β c.1) (β (D.σ c.1)) := by
  unfold weight firsts
  exact Finset.prod_subtype _ (fun i => by simp) (fun i => tcoef (β i) (β (D.σ i)))

lemma sum_pairs {M : Type*} [AddCommMonoid M] (f : Fin (2 * n) → M) :
    ∑ i, f i = ∑ c : D.Chord, (f c.1 + f (D.σ c.1)) := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => i < D.σ i), Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_subtype _ (fun i => by simp) f
  · apply Finset.sum_nbij' (fun p => D.chordOf p) (fun c => D.σ c.1)
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

lemma σ_ne_first {c c' : D.Chord} (h : c' ≠ c) : D.σ c'.1 ≠ c.1 := by
  intro e
  have h1 : c'.1 = D.σ c.1 := by rw [← e, D.invol]
  have a1 : c'.1 < c.1 := by have := c'.2; rwa [e] at this
  have a2 : c.1 < c'.1 := by have := c.2; rwa [← h1] at this
  exact lt_asymm a1 a2

lemma first_ne_second (c c' : D.Chord) : c'.1 ≠ D.σ c.1 := by
  intro e
  have a1 : c'.1 < c.1 := by
    have := c'.2; rw [e, D.invol] at this; rw [e]; exact this
  have a2 := c.2
  rw [e] at a1
  exact lt_asymm a1 a2

lemma first_ne_of_ne {c c' : D.Chord} (h : c' ≠ c) : c'.1 ≠ c.1 :=
  fun e => h (Subtype.ext e)

lemma weight_update_first (γ : Fin (2 * n) → Fin 3) (c : D.Chord) (a : Fin 3) :
    D.weight (Function.update γ c.1 a) = tcoef a (γ (D.σ c.1)) *
      ∏ c' ∈ univ.erase c, tcoef (γ c'.1) (γ (D.σ c'.1)) := by
  rw [weight_eq, ← Finset.mul_prod_erase univ _ (mem_univ c)]
  congr 1
  · rw [Function.update_self, Function.update_of_ne (D.nofix c.1)]
  · apply Finset.prod_congr rfl
    intro c' hc'
    have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
    rw [Function.update_of_ne (D.first_ne_of_ne hne), Function.update_of_ne (D.σ_ne_first hne)]

lemma weight_update_second (γ : Fin (2 * n) → Fin 3) (c : D.Chord) (a : Fin 3) :
    D.weight (Function.update γ (D.σ c.1) a) = tcoef (γ c.1) a *
      ∏ c' ∈ univ.erase c, tcoef (γ c'.1) (γ (D.σ c'.1)) := by
  rw [weight_eq, ← Finset.mul_prod_erase univ _ (mem_univ c)]
  congr 1
  · rw [Function.update_self, Function.update_of_ne (D.first_ne_second c c)]
  · apply Finset.prod_congr rfl
    intro c' hc'
    have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
    rw [Function.update_of_ne (D.first_ne_second c c')]
    rw [Function.update_of_ne]
    intro e
    exact D.first_ne_of_ne hne (by have := congrArg D.σ e; rwa [D.invol, D.invol] at this)

lemma sum_update_weight (γ : Fin (2 * n) → Fin 3) :
    ∑ i, ∑ a, D.weight (Function.update γ i a) * cF a (γ i) = 0 := by
  rw [D.sum_pairs]
  apply Finset.sum_eq_zero
  intro c _
  simp only [D.weight_update_first, D.weight_update_second]
  have h := tcoef_invariant (γ c.1) (γ (D.σ c.1))
  set R := ∏ c' ∈ univ.erase c, tcoef (γ c'.1) (γ (D.σ c'.1))
  have e1 : ∑ a, tcoef a (γ (D.σ c.1)) * R * cF a (γ c.1) =
      R * ∑ a, tcoef a (γ (D.σ c.1)) * cF a (γ c.1) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  have e2 : ∑ a, tcoef (γ c.1) a * R * cF a (γ (D.σ c.1)) =
      R * ∑ a, tcoef (γ c.1) a * cF a (γ (D.σ c.1)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e1, e2, ← mul_add, h, mul_zero]

lemma sum_reindex {A : Type*} [AddCommMonoid A] (i : Fin (2 * n)) (G : (Fin (2 * n) → Fin 3) → Fin 3 → A) :
    ∑ β : Fin (2 * n) → Fin 3, ∑ b : Fin 3, G β b =
      ∑ γ : Fin (2 * n) → Fin 3, ∑ a : Fin 3, G (Function.update γ i a) (γ i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin (2 * n) → Fin 3) × Fin 3 ≃ (Fin (2 * n) → Fin 3) × Fin 3 :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  exact Fintype.sum_equiv e _ _ (fun p => by simp [e])

/-- The Casimir element of a chord diagram commutes with `F`. -/
theorem casimir_comm {A : Type*} [Ring A] [Algebra ℚ A] (x : Fin 3 → A) (hx : ∀ a, x 1 * x a - x a * x 1 = ∑ b, cF a b • x b) :
    x 1 * D.casimirWord x = D.casimirWord x * x 1 := by
  rw [← sub_eq_zero]
  unfold casimirWord
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, comm_prod_ofFn, hx, prod_update_sum]
  have e : ∀ (β : Fin (2 * n) → Fin 3) i b,
      Function.update (fun j => x (β j)) i (x b) = fun j => x (Function.update β i b j) := by
    intro β i b
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [e, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have step : ∀ i : Fin (2 * n), ∑ β : Fin (2 * n) → Fin 3, ∑ b, (D.weight β * cF (β i) b) •
      (List.ofFn fun j => x (Function.update β i b j)).prod =
      ∑ γ : Fin (2 * n) → Fin 3, (∑ a, D.weight (Function.update γ i a) * cF a (γ i)) •
        (List.ofFn fun j => x (γ j)).prod := by
    intro i
    rw [sum_reindex i (fun β b => (D.weight β * cF (β i) b) •
      (List.ofFn fun j => x (Function.update β i b j)).prod)]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a _
    simp [Function.update_idem, Function.update_eq_self]
  rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_comm]
  simp_rw [← Finset.sum_smul, D.sum_update_weight, zero_smul, Finset.sum_const_zero]

end ChordDiagram

end SL2W
