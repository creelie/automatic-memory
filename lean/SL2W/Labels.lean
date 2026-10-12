import SL2W.Words

/-!
# Label words: the loop polynomial and its fermionic realisation
-/

open Finset

namespace SL2W

lemma splits_map {γ δ : Type*} (f : γ → δ) (l : List γ) :
    splits (l.map f) = (splits l).map (fun s => (s.1.map f, f s.2.1, s.2.2.map f)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, Function.comp_def]

lemma sum_list_comm {ι γ M : Type*} [Fintype ι] [AddCommMonoid M] (l : List γ) (g : ι → γ → M) :
    ∑ i, (l.map (g i)).sum = (l.map fun s => ∑ i, g i s).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

lemma intCast_list_sum (l : List ℤ) : ((l.sum : ℤ) : ℚ) = (l.map (fun x : ℤ => (Int.cast x : ℚ))).sum := by
  induction l <;> simp [*]

lemma length_of_mem_splits {γ : Type*} {l : List γ} {s : List γ × γ × List γ}
    (hs : s ∈ splits l) : s.1.length + s.2.2.length + 1 = l.length := by
  have h := congrArg List.length (splits_spec l s hs)
  simp at h; omega

section Labels

variable {α : Type*} [LinearOrder α]

/-- Rename the label `v` to `u`. -/
def rename (v u x : α) : α := if x = v then u else x

lemma rename_self (u x : α) : rename u u x = x := by
  unfold rename; split_ifs with h <;> simp [h]

lemma map_rename_self (u : α) (l : List α) : l.map (rename u u) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [rename_self, ih]

lemma not_mem_map_rename {v u : α} (h : v ≠ u) (l : List α) : v ∉ l.map (rename v u) := by
  simp only [List.mem_map, not_exists, not_and]
  intro x _ hx
  unfold rename at hx
  split_ifs at hx with hxv
  · exact h hx.symm
  · exact hxv hx

lemma count_map_rename {v u : α} (h : v ≠ u) (a : α) (l : List α) :
    (l.map (rename v u)).count a =
      if a = u then l.count u + l.count v else if a = v then 0 else l.count a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq, rename]
    by_cases hxv : x = v
    · subst hxv; by_cases hau : a = u
      · subst hau; simp [h]; omega
      · simp [hau, Ne.symm hau]; split_ifs <;> simp_all
    · by_cases hau : a = u
      · subst hau; simp [hxv]; split_ifs <;> simp_all <;> omega
      · simp [hxv, hau]; split_ifs <;> simp_all

/-- Every label of the list occurs exactly twice. -/
def DO (L : List α) : Prop := ∀ a ∈ L, L.count a = 2

lemma DO_erase_self {u : α} {A B : List α} (h : DO (u :: (A ++ u :: B))) : DO (A ++ B) := by
  intro a ha
  have h1 := h a (by simp at ha ⊢; tauto)
  simp only [List.count_cons, List.count_append, beq_iff_eq] at h1
  have hpos : 0 < (A ++ B).count a := List.count_pos_iff.mpr ha
  rw [List.count_append] at hpos ⊢
  by_cases hau : u = a
  · subst hau; simp at h1; omega
  · simp [hau] at h1; omega

lemma DO_contract {u x : α} {A B : List α} (h : DO (u :: (A ++ x :: B))) (hxu : x ≠ u) :
    DO ((A ++ B).map (rename x u)) := by
  intro a ha
  have hu := h u (by simp)
  have hx := h x (by simp)
  simp only [List.count_cons, List.count_append, beq_iff_eq, hxu, Ne.symm hxu,
    if_false, if_true] at hu hx
  rw [count_map_rename hxu]
  by_cases hau : a = u
  · subst hau; simp [List.count_append]; omega
  · have hax : a ≠ x := fun e => not_mem_map_rename hxu _ (e ▸ ha)
    simp only [hau, hax, if_false]
    have hpos : 0 < ((A ++ B).map (rename x u)).count a := List.count_pos_iff.mpr ha
    rw [count_map_rename hxu] at hpos
    simp only [hau, hax, if_false] at hpos
    have ha' := h a (by
      have : a ∈ A ++ B := List.count_pos_iff.mp hpos
      simp at this ⊢; tauto)
    simp only [List.count_cons, List.count_append, beq_iff_eq, Ne.symm hau, Ne.symm hax,
      if_false] at ha'
    rw [List.count_append]; omega

/-- The loop polynomial of a word of labels. -/
noncomputable def Pol : List α → Polynomial ℚ
  | [] => 1
  | u :: W => ((splits W).attach.map fun s =>
      (-1) ^ s.1.1.length * (if s.1.2.1 = u then Polynomial.X else 1) *
        Pol ((s.1.1 ++ s.1.2.2).map (rename s.1.2.1 u))).sum
termination_by L => L.length
decreasing_by
  have h := congrArg List.length (splits_spec W s.1 s.2)
  simp at h ⊢; omega

@[simp] lemma Pol_nil : Pol ([] : List α) = 1 := by rw [Pol]

lemma Pol_cons (u : α) (W : List α) : Pol (u :: W) = ((splits W).map fun s =>
      (-1) ^ s.1.length * (if s.2.1 = u then Polynomial.X else 1) *
        Pol ((s.1 ++ s.2.2).map (rename s.2.1 u))).sum := by
  rw [Pol.eq_2]; simp [List.map_attach_eq_pmap]

lemma map_rename_of_not_mem {v u : α} {l : List α} (h : v ∉ l) : l.map (rename v u) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    simp [rename, Ne.symm h.1, ih h.2]

lemma τF_DO {L : List α} (h : DO L) : τF L = (-1) ^ inv L := by
  unfold τF
  rw [if_pos]
  intro c
  by_cases hc : c ∈ L
  · rw [h c hc]; exact even_two
  · rw [List.count_eq_zero_of_not_mem hc]; exact ⟨0, rfl⟩

lemma τF_DO_sq {L : List α} (h : DO L) : τF L * τF L = 1 := by
  rw [τF_DO h, ← pow_add, ← two_mul, pow_mul]; norm_num

lemma τF_uvvu (R1 R2 R3 : List α) {u v : α} (hv1 : v ∉ R1) (hv2 : v ∉ R2) (hv3 : v ∉ R3)
    (hu1 : u ∉ R1) (hu2 : u ∉ R2) :
    τF (u :: v :: (R1 ++ v :: (R2 ++ u :: R3))) =
      τF ((R1 ++ v :: (R2 ++ u :: R3)).map (rename v u)) := by
  have hm : (R1 ++ v :: (R2 ++ u :: R3)).map (rename v u) = R1 ++ u :: (R2 ++ u :: R3) := by
    simp [map_rename_of_not_mem hv1, map_rename_of_not_mem hv2, map_rename_of_not_mem hv3,
      rename]
  have e1 := τF_pair [u] R1 (R2 ++ u :: R3) v
  have e2 := τF_pair [] (R1 ++ R2) R3 u
  have e3 := τF_pair R1 R2 R3 u
  simp only [List.singleton_append] at e1
  simp only [List.nil_append, List.append_assoc] at e2
  rw [hm, e1, e2, e3]
  simp only [List.length_append, List.count_append, List.count_eq_zero_of_not_mem hv1,
    List.count_eq_zero_of_not_mem hu1, List.count_eq_zero_of_not_mem hu2, add_zero]
  rw [← mul_assoc, ← pow_add]
  congr 1
  exact neg_one_pow_congr (by omega)

lemma τF_uvuv (R1 R2 R3 : List α) {u v : α} (huv : u ≠ v) (hv1 : v ∉ R1) (hv2 : v ∉ R2)
    (hv3 : v ∉ R3) (hu1 : u ∉ R1) (hu2 : u ∉ R2) :
    τF (u :: v :: (R1 ++ u :: (R2 ++ v :: R3))) =
      -τF ((R1 ++ u :: (R2 ++ v :: R3)).map (rename v u)) := by
  have hm : (R1 ++ u :: (R2 ++ v :: R3)).map (rename v u) = R1 ++ u :: (R2 ++ u :: R3) := by
    simp [map_rename_of_not_mem hv1, map_rename_of_not_mem hv2, map_rename_of_not_mem hv3,
      rename]
  have e1 := τF_pair [u] (R1 ++ u :: R2) R3 v
  have e2 := τF_pair [] R1 (R2 ++ R3) u
  have e3 := τF_pair R1 R2 R3 u
  simp only [List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] at e1
  simp only [List.nil_append] at e2
  have hc : (R1 ++ u :: R2).count v = 0 :=
    List.count_eq_zero_of_not_mem (by simp [hv1, hv2, Ne.symm huv])
  rw [hm, e1, hc, e2, e3]
  simp only [List.length_append, List.length_cons, List.count_eq_zero_of_not_mem hu1,
    List.count_eq_zero_of_not_mem hu2, add_zero]
  rw [← mul_assoc, ← pow_add]
  have : (-1 : ℤ) ^ (R1.length + (R2.length + 1) + R1.length) = -(-1) ^ R2.length := by
    rw [neg_one_pow_congr (show (R1.length + (R2.length + 1) + R1.length) % 2 =
      (R2.length + 1) % 2 by omega), pow_succ]
    ring
  rw [this]
  ring

lemma filter_uv_nil {u v : α} {l : List α} (hu : u ∉ l) (hv : v ∉ l) :
    l.filter (fun x => x = u ∨ x = v) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq, not_or]
  exact ⟨fun h => hu (h ▸ hx), fun h => hv (h ▸ hx)⟩

lemma filter_uv_nil' {u v : α} {l : List α} (hu : u ∉ l) (hv : v ∉ l) :
    l.filter (fun x => decide (x = u) || decide (x = v)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
  exact ⟨fun h => hu (h ▸ hx), fun h => hv (h ▸ hx)⟩

/-- The sign of a list starting with two distinct labels that each occur once more. -/
lemma τF_head_pair (R : List α) {u v : α} (huv : u ≠ v) (hu : R.count u = 1)
    (hv : R.count v = 1) :
    τF (u :: v :: R) = (if R.filter (fun x => x = u ∨ x = v) = [u, v] then -1 else 1) *
      τF (R.map (rename v u)) := by
  have hu' : u ∈ R := List.count_pos_iff.mp (by omega)
  obtain ⟨S, T, rfl⟩ := List.append_of_mem hu'
  have hcu := hu
  simp only [List.count_append, List.count_cons_self] at hcu
  have hS : u ∉ S := fun h => by have := List.count_pos_iff.mpr h; omega
  have hT : u ∉ T := fun h => by have := List.count_pos_iff.mpr h; omega
  have hvmem : v ∈ S ++ u :: T := List.count_pos_iff.mp (by omega)
  have hvST : v ∈ S ∨ v ∈ T := by
    simp only [List.mem_append, List.mem_cons] at hvmem
    rcases hvmem with h | h | h
    · exact Or.inl h
    · exact absurd h.symm huv
    · exact Or.inr h
  rcases hvST with hvS | hvT
  · obtain ⟨R1, R2, rfl⟩ := List.append_of_mem hvS
    have hcv := hv
    simp only [List.count_append, List.count_cons_self, List.count_cons, beq_iff_eq,
      if_neg huv] at hcv
    have hv1 : v ∉ R1 := fun h => by have := List.count_pos_iff.mpr h; omega
    have hv2 : v ∉ R2 := fun h => by have := List.count_pos_iff.mpr h; omega
    have hv3 : v ∉ T := fun h => by have := List.count_pos_iff.mpr h; omega
    have hu1 : u ∉ R1 := fun h => hS (by simp [h])
    have hu2 : u ∉ R2 := fun h => hS (by simp [h])
    have hfilt : ((R1 ++ v :: R2) ++ u :: T).filter (fun x => x = u ∨ x = v) = [v, u] := by
      simp [List.filter_append, List.filter_cons, filter_uv_nil' hu1 hv1,
        filter_uv_nil' hu2 hv2, filter_uv_nil' hT hv3]
    rw [hfilt, if_neg (by simp [Ne.symm huv]), one_mul]
    have := τF_uvvu R1 R2 T hv1 hv2 hv3 hu1 hu2
    simpa [List.append_assoc] using this
  · obtain ⟨R2, R3, rfl⟩ := List.append_of_mem hvT
    have hcv := hv
    simp only [List.count_append, List.count_cons_self, List.count_cons, beq_iff_eq,
      if_neg huv] at hcv
    have hv1 : v ∉ S := fun h => by have := List.count_pos_iff.mpr h; omega
    have hv2 : v ∉ R2 := fun h => by have := List.count_pos_iff.mpr h; omega
    have hv3 : v ∉ R3 := fun h => by have := List.count_pos_iff.mpr h; omega
    have hu2 : u ∉ R2 := fun h => hT (by simp [h])
    have hu3 : u ∉ R3 := fun h => hT (by simp [h])
    have hfilt : (S ++ u :: (R2 ++ v :: R3)).filter (fun x => x = u ∨ x = v) = [u, v] := by
      simp [List.filter_append, List.filter_cons, filter_uv_nil' hS hv1,
        filter_uv_nil' hu2 hv2, filter_uv_nil' hu3 hv3]
    rw [hfilt, if_pos rfl]
    have := τF_uvuv S R2 R3 huv hv1 hv2 hv3 hS hu2
    rw [this]
    ring

section Colour

variable [Fintype α]

/-- The fermionic colour sum of a word of labels. -/
noncomputable def Gf (N : ℕ) (L : List α) : ℚ := ∑ col : α → Fin N, (τF (L.map col) : ℚ)

lemma fiber_sum (N : ℕ) (u v : α) (hvu : v ≠ u) (G : (α → Fin N) → ℚ)
    (hG : ∀ col c, G (Function.update col v c) = G col) :
    (N : ℚ) * ∑ col : α → Fin N, (if col v = col u then G col else 0) = ∑ col, G col := by
  have key : ∀ c : Fin N, ∑ col : α → Fin N, (if col v = c then G col else 0) =
      ∑ col : α → Fin N, (if col v = col u then G col else 0) := by
    intro c
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun col => Function.update col v (col u))
      (fun col => Function.update col v c) ?_ ?_ ?_ ?_ ?_
    · intro col _
      simp [Function.update_apply, Ne.symm hvu]
    · intro col _
      simp
    · intro col hcol
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcol
      ext y
      by_cases hy : y = v
      · subst hy; simp [hcol]
      · simp [Function.update_apply, hy]
    · intro col hcol
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcol
      ext y
      by_cases hy : y = v
      · subst hy; simp [Function.update_apply, Ne.symm hvu, hcol]
      · simp [Function.update_apply, hy]
    · intro col _
      exact (hG col (col u)).symm
  calc (N : ℚ) * ∑ col : α → Fin N, (if col v = col u then G col else 0)
      = ∑ c : Fin N, ∑ col : α → Fin N, (if col v = col u then G col else 0) := by simp
    _ = ∑ c : Fin N, ∑ col : α → Fin N, (if col v = c then G col else 0) := by
        simp_rw [key]
    _ = ∑ col : α → Fin N, ∑ c : Fin N, (if col v = c then G col else 0) := Finset.sum_comm
    _ = ∑ col, G col := by simp

theorem Gf_Pol (N : ℕ) : ∀ (m : ℕ) (L : List α), L.length = 2 * m → DO L →
    (N : ℚ) ^ m * Gf N L = (N : ℚ) ^ Fintype.card α * (Pol L).eval (N : ℚ)
  | 0, L, hL, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [Gf, τF]
  | m + 1, [], hL, _ => by simp at hL
  | m + 1, u :: W, hL, hDO => by
    have hW : ∀ s ∈ splits W, (s.1 ++ s.2.2).length = 2 * m := by
      intro s hs
      have := length_of_mem_splits hs
      simp at hL ⊢; omega
    have expand : Gf N (u :: W) = ((splits W).map fun s => ((-1 : ℚ) ^ s.1.length *
        ∑ col : α → Fin N, if col s.2.1 = col u then (τF ((s.1 ++ s.2.2).map col) : ℚ)
          else 0)).sum := by
      have hw : ∀ col : α → Fin N, τF ((u :: W).map col) = ((splits W).map fun s =>
          (-1 : ℤ) ^ s.1.length * if col s.2.1 = col u then τF ((s.1 ++ s.2.2).map col)
            else 0).sum := by
        intro col
        rw [List.map_cons, τF_wick, splits_map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro s _
        simp only [Function.comp_apply, List.length_map, ← List.map_append]
      unfold Gf
      rw [show (fun s : List α × α × List α => ((-1 : ℚ) ^ s.1.length *
          ∑ col : α → Fin N, if col s.2.1 = col u then (τF ((s.1 ++ s.2.2).map col) : ℚ)
            else 0)) = fun s => ∑ col : α → Fin N, ((-1 : ℚ) ^ s.1.length *
          if col s.2.1 = col u then (τF ((s.1 ++ s.2.2).map col) : ℚ) else 0) from
        funext fun s => Finset.mul_sum _ _ _]
      rw [← sum_list_comm]
      apply Finset.sum_congr rfl
      intro col _
      rw [hw col, intCast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro s _
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring
    rw [expand, Pol_cons, Polynomial.eval_listSum, List.map_map, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro s hs
    have hsp := splits_spec W s hs
    rw [← hsp] at hDO
    simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one]
    by_cases hx : s.2.1 = u
    · rw [hx] at hDO ⊢
      simp only [if_true, Polynomial.eval_X, map_rename_self]
      have ih := Gf_Pol N m (s.1 ++ s.2.2) (hW s hs) (DO_erase_self hDO)
      unfold Gf at ih
      rw [pow_succ]
      linear_combination ((-1 : ℚ) ^ s.1.length * (N : ℚ)) * ih
    · simp only [hx, if_false, Polynomial.eval_one, mul_one]
      set C := (s.1 ++ s.2.2).map (rename s.2.1 u)
      have hC : ∀ col : α → Fin N, col s.2.1 = col u →
          (s.1 ++ s.2.2).map col = C.map col := by
        intro col hcol
        simp only [C, List.map_map]
        apply List.map_congr_left
        intro y _
        simp only [Function.comp_apply, rename]
        split_ifs with hy
        · rw [hy, hcol]
        · rfl
      have hsum : ∑ col : α → Fin N, (if col s.2.1 = col u then
            (τF ((s.1 ++ s.2.2).map col) : ℚ) else 0) =
          ∑ col : α → Fin N, (if col s.2.1 = col u then (τF (C.map col) : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro col _
        split_ifs with h
        · rw [hC col h]
        · rfl
      have hfib := fiber_sum N u s.2.1 hx (fun col => (τF (C.map col) : ℚ)) (by
        intro col c
        congr 2
        apply List.map_congr_left
        intro y hy
        have : y ≠ s.2.1 := fun e => not_mem_map_rename hx _ (e ▸ hy)
        simp [Function.update_apply, this])
      have hCl : C.length = 2 * m := by
        have := hW s hs
        simp only [List.length_append] at this
        simp only [C, List.length_map, List.length_append]; omega
      have ih := Gf_Pol N m C hCl (DO_contract hDO hx)
      unfold Gf at ih
      rw [hsum]
      linear_combination ((-1 : ℚ) ^ s.1.length) * ih +
        ((-1 : ℚ) ^ s.1.length * (N : ℚ) ^ m) * hfib

end Colour

end Labels

end SL2W
