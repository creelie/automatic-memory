import SL2W.Defs

/-!
# Counting `2`-subset assignments

Sums of `edgeSign` over all assignments of `2`-element subsets of `{0, …, N-1}` to the
vertices, grouped by the set of used elements, and the polynomial `Sp` interpolating them.
-/

open Finset

namespace SL2W

section Graphs

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma T_eq_zero (G : SimpleGraph V) {k : ℕ} (hk : 2 * Fintype.card V < k) : T k G = 0 := by
  unfold T
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  rintro ⟨h2, hU⟩
  have h := Finset.card_biUnion_le (s := (univ : Finset V)) (t := p)
  rw [hU, card_univ, Fintype.card_fin] at h
  simp only [h2, sum_const, card_univ, smul_eq_mul] at h
  omega

omit [DecidableEq V] in
lemma edgeSign_map (G : SimpleGraph V) {k N : ℕ} (f : Fin k ↪ Fin N) (q : V → Finset (Fin k)) :
    edgeSign G (fun v => (q v).map f) = edgeSign G q := by
  unfold edgeSign
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.lift_mk]
    rw [← Finset.map_inter, Finset.card_map]

lemma sum_relabel (G : SimpleGraph V) {N : ℕ} (U : Finset (Fin N)) :
    ∑ p ∈ univ.filter (fun p : V → Finset (Fin N) => univ.biUnion p = U),
      (if ∀ v, (p v).card = 2 then edgeSign G p else 0) = T U.card G := by
  set emb := U.orderEmbOfFin rfl with hemb
  have hmem : ∀ j, emb j ∈ U := fun j => U.orderEmbOfFin_mem rfl j
  have hrange : ∀ x ∈ U, ∃ j, emb j = x := by
    intro x hx
    have : x ∈ Set.range emb := by rw [hemb, Finset.range_orderEmbOfFin]; exact hx
    exact this
  unfold T
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_filter]
  symm
  apply Finset.sum_nbij' (fun q v => (q v).map emb.toEmbedding)
    (fun p v => univ.filter (fun j => emb j ∈ p v))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨?_, fun v => by rw [Finset.card_map]; exact hq.1 v⟩
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨v, j, _, rfl⟩; exact hmem j
    · intro hx
      obtain ⟨j, rfl⟩ := hrange x hx
      have : j ∈ univ.biUnion q := by rw [hq.2]; exact mem_univ j
      obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp this
      exact ⟨v, j, hv, rfl⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hsub : ∀ v, p v ⊆ U := by
      intro v x hx
      rw [← hp.1]
      exact Finset.mem_biUnion.mpr ⟨v, mem_univ v, hx⟩
    have hmap : ∀ v, (univ.filter (fun j => emb j ∈ p v)).map emb.toEmbedding = p v := by
      intro v
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        RelEmbedding.coe_toEmbedding]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hx
        obtain ⟨j, rfl⟩ := hrange x (hsub v hx)
        exact ⟨j, hx, rfl⟩
    refine ⟨fun v => ?_, ?_⟩
    · rw [← Finset.card_map emb.toEmbedding, hmap v]; exact hp.2 v
    · ext j
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, iff_true]
      have : emb j ∈ univ.biUnion p := by rw [hp.1]; exact hmem j
      obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp this
      exact ⟨v, hv⟩
  · intro q _
    funext v
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨a, ha, e⟩; rwa [emb.injective e] at ha
    · intro hj; exact ⟨j, hj, rfl⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    funext v
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx
      have : x ∈ U := by
        rw [← hp.1]; exact Finset.mem_biUnion.mpr ⟨v, mem_univ v, hx⟩
      obtain ⟨j, rfl⟩ := hrange x this
      exact ⟨j, hx, rfl⟩
  · intro q _
    exact (edgeSign_map G emb.toEmbedding q).symm

theorem sum_card_two (G : SimpleGraph V) (N : ℕ) :
    ∑ p : V → Finset (Fin N), (if ∀ v, (p v).card = 2 then edgeSign G p else 0) =
      ∑ k ∈ range (N + 1), (N.choose k : ℤ) * T k G := by
  rw [← Finset.sum_fiberwise univ (fun p : V → Finset (Fin N) => univ.biUnion p)]
  simp_rw [sum_relabel]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => T k G)]
  simp [nsmul_eq_mul]

lemma card_pair_inter {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    (({a, b} : Finset α) ∩ {c, d}).card =
      (if a = c then 1 else 0) + (if a = d then 1 else 0) + (if b = c then 1 else 0) +
        (if b = d then 1 else 0) := by
  rw [← Finset.filter_mem_eq_inter, Finset.card_filter, Finset.sum_pair hab]
  have key : ∀ x, (if x ∈ ({c, d} : Finset α) then 1 else 0) =
      (if x = c then 1 else 0) + (if x = d then 1 else 0) := by
    intro x
    by_cases hc : x = c
    · subst hc; simp [hcd]
    · by_cases hd : x = d
      · subst hd; simp [hc]
      · simp [hc, hd]
  rw [key, key]
  ring

lemma sum_pair_count (N : ℕ) (s : Finset (Fin N)) :
    ∑ x : Fin N × Fin N, (if x.1 ≠ x.2 ∧ ({x.1, x.2} : Finset (Fin N)) = s then (1 : ℤ) else 0) =
      if s.card = 2 then 2 else 0 := by
  split_ifs with hs
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
    rw [← Finset.sum_filter]
    have e : (univ.filter fun x : Fin N × Fin N =>
        x.1 ≠ x.2 ∧ ({x.1, x.2} : Finset (Fin N)) = {a, b}) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨hxy, e⟩
        have hx : x ∈ ({a, b} : Finset (Fin N)) := e ▸ (by simp)
        have hy : y ∈ ({a, b} : Finset (Fin N)) := e ▸ (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hab, rfl⟩
        · exact ⟨hab.symm, Finset.pair_comm _ _⟩
    rw [e, Finset.sum_pair (by simp [hab])]
    norm_num
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    rintro ⟨hx, rfl⟩
    exact hs (Finset.card_pair hx)

/-- Summing over ordered pairs of distinct colours instead of `2`-subsets. -/
lemma sum_pairs_fiber (N : ℕ) (E : (V → Finset (Fin N)) → ℤ) :
    ∑ κ : V → Fin N × Fin N,
        (if ∀ c, (κ c).1 ≠ (κ c).2 then E (fun c => {(κ c).1, (κ c).2}) else 0) =
      2 ^ Fintype.card V * ∑ p : V → Finset (Fin N), (if ∀ v, (p v).card = 2 then E p else 0) := by
  have step : ∀ κ : V → Fin N × Fin N,
      (if ∀ c, (κ c).1 ≠ (κ c).2 then E (fun c => {(κ c).1, (κ c).2}) else 0) =
        ∑ p : V → Finset (Fin N), E p * ∏ v, (if (κ v).1 ≠ (κ v).2 ∧
          ({(κ v).1, (κ v).2} : Finset (Fin N)) = p v then (1 : ℤ) else 0) := by
    intro κ
    by_cases h : ∀ c, (κ c).1 ≠ (κ c).2
    · rw [if_pos h]
      simp_rw [Finset.prod_boole]
      simp only [Finset.mem_univ, true_imp_iff, h, true_and, ne_eq, not_false_eq_true]
      have e : ∀ p : V → Finset (Fin N),
          (∀ v, ({(κ v).1, (κ v).2} : Finset (Fin N)) = p v) ↔
          (fun c => ({(κ c).1, (κ c).2} : Finset (Fin N))) = p := fun p => funext_iff.symm
      simp_rw [e, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    · rw [if_neg h]
      simp only [not_forall, not_not] at h
      obtain ⟨c, hc⟩ := h
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [Finset.prod_eq_zero (mem_univ c) (by simp [hc]), mul_zero]
  simp_rw [step]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum]
  have hps : (∑ κ : V → Fin N × Fin N, ∏ v, (if (κ v).1 ≠ (κ v).2 ∧
      ({(κ v).1, (κ v).2} : Finset (Fin N)) = p v then (1 : ℤ) else 0)) =
      ∏ v, ∑ x : Fin N × Fin N, (if x.1 ≠ x.2 ∧ ({x.1, x.2} : Finset (Fin N)) = p v
        then (1 : ℤ) else 0) := (Fintype.prod_sum (fun v (x : Fin N × Fin N) =>
          if x.1 ≠ x.2 ∧ ({x.1, x.2} : Finset (Fin N)) = p v then (1 : ℤ) else 0)).symm
  rw [hps]
  simp_rw [sum_pair_count]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_imp_iff, Finset.prod_const, Finset.card_univ]
  split_ifs <;> ring

end Graphs

section Sp

open Polynomial

variable {V : Type} [Fintype V]

/-- The polynomial `∑ₖ Tₖ(G) · C(X, k)`. -/
noncomputable def Sp (G : SimpleGraph V) : ℚ[X] :=
  ∑ k ∈ range (2 * Fintype.card V + 1), C ((T k G : ℚ) / k.factorial) * descPochhammer ℚ k

lemma Sp_eval_nat (G : SimpleGraph V) (N : ℕ) :
    (Sp G).eval (N : ℚ) = ∑ k ∈ range (N + 1), (N.choose k : ℚ) * T k G := by
  unfold Sp
  rw [eval_finset_sum]
  simp only [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have e : ∀ k, (T k G : ℚ) / k.factorial * ((k.factorial * N.choose k : ℕ) : ℚ) =
      (N.choose k : ℚ) * T k G := by
    intro k
    have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    push_cast
    field_simp
  simp_rw [e]
  have h1 : ∑ k ∈ range (2 * Fintype.card V + 1), (N.choose k : ℚ) * T k G =
      ∑ k ∈ range (N + 2 * Fintype.card V + 1), (N.choose k : ℚ) * T k G := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [T_eq_zero G (by omega)]; simp
  have h2 : ∑ k ∈ range (N + 1), (N.choose k : ℚ) * T k G =
      ∑ k ∈ range (N + 2 * Fintype.card V + 1), (N.choose k : ℚ) * T k G := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h1, h2]

lemma descPochhammer_eval_neg_two (k : ℕ) :
    (descPochhammer ℚ k).eval (-2) = (-1) ^ k * ((k + 1).factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast,
      Nat.factorial_succ (k + 1)]
    push_cast
    ring

lemma Sp_eval_neg_two (G : SimpleGraph V) :
    (Sp G).eval (-2) =
      ∑ k ∈ range (2 * Fintype.card V + 1), (-1 : ℚ) ^ k * (k + 1) * (T k G : ℚ) := by
  unfold Sp
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_mul, eval_C, descPochhammer_eval_neg_two, Nat.factorial_succ]
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp

lemma ξ_eq_Sp (G : SimpleGraph V) :
    ξ G = (Sp G).eval (-2) / (-32 : ℚ) ^ Fintype.card V := by
  rw [Sp_eval_neg_two]; rfl

end Sp

end SL2W
