import SL2W.Labels

/-!
# Words made of two-letter blocks

The fermionic sign of a word obtained by replacing every letter of a Gauss word by a block
of two distinct letters, and the effect of reversing some of the blocks.
-/

open Finset

namespace SL2W

section Move

variable {β : Type*} [LinearOrder β]

/-- Moving a two-letter block to the left past a word. -/
lemma τF_block_move (P A S : List β) (x y : β) :
    τF (P ++ (A ++ x :: y :: S)) =
      (-1) ^ (A.count x + A.count y) * τF (P ++ x :: y :: (A ++ S)) := by
  rw [τF_move P A (y :: S) x]
  have h := τF_move (P ++ [x]) A S y
  simp only [List.append_assoc, List.singleton_append] at h
  rw [h, ← mul_assoc, ← pow_add]
  congr 1
  exact neg_one_pow_congr (by omega)

/-- A block, reversed when its flag is set. -/
def blk (w : β × β × Bool) : List β := if w.2.2 then [w.2.1, w.1] else [w.1, w.2.1]

/-- The block in its original order. -/
def blk0 (w : β × β × Bool) : List β := [w.1, w.2.1]

/-- The sign produced by reversing a block. -/
def flipSign (w : β × β × Bool) : ℤ := if w.2.2 = true ∧ w.1 ≠ w.2.1 then -1 else 1

lemma τF_flip : ∀ (ws : List (β × β × Bool)) (P : List β),
    τF (P ++ ws.flatMap blk) = (ws.map flipSign).prod * τF (P ++ ws.flatMap blk0)
  | [], P => by simp
  | (x, y, f) :: ws, P => by
    simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
    have key : ∀ R, τF (P ++ (blk (x, y, f) ++ R)) =
        flipSign (x, y, f) * τF (P ++ (blk0 (x, y, f) ++ R)) := by
      intro R
      unfold blk blk0 flipSign
      by_cases hf : f = true
      · by_cases hxy : x = y
        · subst hxy; simp [hf]
        · simp only [hf, if_true, ne_eq, hxy, not_false_eq_true, and_self, List.cons_append,
            List.nil_append]
          rw [τF_swap P R (Ne.symm hxy)]
          ring
      · simp [hf]
    rw [show P ++ (blk (x, y, f) ++ ws.flatMap blk) = (P ++ blk (x, y, f)) ++ ws.flatMap blk
        from (List.append_assoc _ _ _).symm, τF_flip ws, List.append_assoc, key]
    ring

end Move

section Crossing

variable {β : Type*} [LinearOrder β] {γ : Type*} [LinearOrder γ] [Fintype γ]

/-- The word of blocks of a Gauss word. -/
def blocks (κ : γ → β × β) (L : List γ) : List β := L.flatMap fun c => [(κ c).1, (κ c).2]

/-- The number of equal pairs between the blocks of two labels. -/
def mpair (κ : γ → β × β) (u v : γ) : ℕ :=
  (if (κ u).1 = (κ v).1 then 1 else 0) + (if (κ u).1 = (κ v).2 then 1 else 0) +
    (if (κ u).2 = (κ v).1 then 1 else 0) + (if (κ u).2 = (κ v).2 then 1 else 0)

/-- `u` and `v` alternate in `L`, starting with `u`. -/
def crs (L : List γ) (u v : γ) : Prop := L.filter (fun x => x = u ∨ x = v) = [u, v, u, v]

instance (L : List γ) (u v : γ) : Decidable (crs L u v) := by unfold crs; infer_instance

/-- The crossing exponent of a Gauss word. -/
def Xc (L : List γ) (m : γ → γ → ℕ) : ℕ := ∑ u, ∑ v, if crs L u v then m u v else 0

lemma Xc_nil (m : γ → γ → ℕ) : Xc [] m = 0 := by
  unfold Xc crs
  simp

lemma blocks_append (κ : γ → β × β) (A B : List γ) :
    blocks κ (A ++ B) = blocks κ A ++ blocks κ B := by
  simp [blocks, List.flatMap_append]

lemma blocks_count (κ : γ → β × β) (u : γ) (A : List γ) :
    (blocks κ A).count (κ u).1 + (blocks κ A).count (κ u).2 =
      (A.map (mpair κ u)).sum := by
  induction A with
  | nil => simp [blocks]
  | cons c A ih =>
    simp only [blocks, List.flatMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.cons_append, List.nil_append, List.count_cons, beq_iff_eq]
    have hm : mpair κ u c = (if (κ u).1 = (κ c).1 then 1 else 0) +
        (if (κ u).1 = (κ c).2 then 1 else 0) + (if (κ u).2 = (κ c).1 then 1 else 0) +
        (if (κ u).2 = (κ c).2 then 1 else 0) := rfl
    rw [hm]
    have e1 : ((κ c).1 = (κ u).1) = ((κ u).1 = (κ c).1) := propext eq_comm
    have e2 : ((κ c).2 = (κ u).1) = ((κ u).1 = (κ c).2) := propext eq_comm
    have e3 : ((κ c).1 = (κ u).2) = ((κ u).2 = (κ c).1) := propext eq_comm
    have e4 : ((κ c).2 = (κ u).2) = ((κ u).2 = (κ c).2) := propext eq_comm
    simp only [e1, e2, e3, e4]
    omega

lemma list_sum_eq_count (A : List γ) (f : γ → ℕ) :
    (A.map f).sum = ∑ v, A.count v * f v := by
  rw [Finset.sum_list_map_count]
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · simp
  · intro v _ hv
    simp [List.count_eq_zero_of_not_mem (by simpa using hv)]

lemma neg_one_pow_count_parity (A : List γ) (f : γ → ℕ) (h : ∀ v, A.count v ≤ 2) :
    (-1 : ℤ) ^ (∑ v, A.count v * f v) = (-1) ^ (∑ v, if A.count v = 1 then f v else 0) := by
  have e : ∑ v, A.count v * f v =
      (∑ v, if A.count v = 1 then f v else 0) + 2 * ∑ v, (if A.count v = 2 then f v else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have := h v
    rcases (by omega : A.count v = 0 ∨ A.count v = 1 ∨ A.count v = 2) with h0 | h1 | h2
    · simp [h0]
    · simp [h1]
    · simp [h2]
  rw [e, pow_add, pow_mul]
  simp

lemma replicate_pattern {u v : γ} (huv : u ≠ v) (a b : ℕ) :
    u :: (List.replicate a v ++ u :: List.replicate b v) = [u, v, u, v] ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    rcases a with _ | _ | a
    · simp at h; exact absurd h.1 huv
    · rcases b with _ | _ | b
      · simp at h
      · simp
      · simp [List.replicate_succ] at h
    · simp [List.replicate_succ] at h
      exact absurd h.1.symm huv
  · rintro ⟨rfl, rfl⟩; rfl

lemma filter_not_mem {u v : γ} {A : List γ} (hA : u ∉ A) :
    A.filter (fun x => x = u ∨ x = v) = List.replicate (A.count v) v := by
  rw [← List.filter_eq]
  apply List.filter_congr
  intro x hx
  have : x ≠ u := fun e => hA (e ▸ hx)
  simp [this]

lemma Xc_cons (m : γ → γ → ℕ) (u : γ) (A B : List γ) (hA : u ∉ A) (hB : u ∉ B)
    (hDO : DO (u :: (A ++ u :: B))) :
    Xc (u :: (A ++ u :: B)) m = (∑ v, if A.count v = 1 then m u v else 0) + Xc (A ++ B) m := by
  have hAB : u ∉ A ++ B := by simp [hA, hB]
  have notcrsAB : ∀ w v, (w = u ∨ v = u) → ¬ crs (A ++ B) w v := by
    intro w v h hc
    have hm : u ∈ (A ++ B).filter (fun x => x = w ∨ x = v) := by
      rw [hc]; rcases h with rfl | rfl <;> simp
    exact hAB (List.mem_of_mem_filter hm)
  have pt : ∀ w v, (if crs (u :: (A ++ u :: B)) w v then m w v else 0) =
      (if crs (A ++ B) w v then m w v else 0) +
        (if w = u then (if A.count v = 1 then m u v else 0) else 0) := by
    intro w v
    by_cases hwu : w = u
    · subst w
      rw [if_neg (notcrsAB _ _ (Or.inl rfl)), zero_add, if_pos rfl]
      by_cases hvu : v = u
      · subst v
        have : ¬ crs (u :: (A ++ u :: B)) u u := by
          unfold crs
          intro hc
          have hf : (u :: (A ++ u :: B)).filter (fun x => x = u ∨ x = u) =
              List.replicate ((u :: (A ++ u :: B)).count u) u := by
            rw [← List.filter_eq]
            apply List.filter_congr
            intro x _
            simp
          rw [hf, hDO u (by simp)] at hc
          simp at hc
        rw [if_neg this, List.count_eq_zero_of_not_mem hA]
        simp
      · have hfL : (u :: (A ++ u :: B)).filter (fun x => x = u ∨ x = v) =
            u :: (List.replicate (A.count v) v ++ u :: List.replicate (B.count v) v) := by
          rw [List.filter_cons_of_pos (by simp), List.filter_append,
            List.filter_cons_of_pos (by simp), filter_not_mem hA, filter_not_mem hB]
        have hiff : crs (u :: (A ++ u :: B)) u v ↔ A.count v = 1 := by
          unfold crs
          rw [hfL, replicate_pattern (Ne.symm hvu)]
          constructor
          · exact fun h => h.1
          · intro h1
            refine ⟨h1, ?_⟩
            have hv : v ∈ u :: (A ++ u :: B) := by
              simp [List.count_pos_iff.mp (by omega : 0 < A.count v)]
            have := hDO v hv
            simp only [List.count_cons, List.count_append, beq_iff_eq, Ne.symm hvu, hvu,
              if_false] at this
            omega
        by_cases h1 : A.count v = 1
        · rw [if_pos (hiff.mpr h1), if_pos h1]
        · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]
    · rw [if_neg hwu, add_zero]
      by_cases hvu : v = u
      · subst v
        rw [if_neg (notcrsAB _ _ (Or.inr rfl))]
        have : ¬ crs (u :: (A ++ u :: B)) w u := by
          unfold crs
          rw [List.filter_cons_of_pos (by simp)]
          intro hc
          simp only [List.cons.injEq] at hc
          exact hwu hc.1.symm
        rw [if_neg this]
      · have hf : (u :: (A ++ u :: B)).filter (fun x => x = w ∨ x = v) =
            (A ++ B).filter (fun x => x = w ∨ x = v) := by
          rw [List.filter_cons_of_neg (by simp [Ne.symm hwu, Ne.symm hvu]), List.filter_append,
            List.filter_cons_of_neg (by simp [Ne.symm hwu, Ne.symm hvu]), List.filter_append]
        have hiff : crs (u :: (A ++ u :: B)) w v ↔ crs (A ++ B) w v := by
          unfold crs; rw [hf]
        by_cases hc : crs (A ++ B) w v
        · rw [if_pos hc, if_pos (hiff.mpr hc)]
        · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]
  unfold Xc
  simp only [pt, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  simp

/-- The sign of a word of blocks of distinct letters along a Gauss word. -/
theorem τF_blocks (κ : γ → β × β) (hκ : ∀ c, (κ c).1 ≠ (κ c).2) :
    ∀ (k : ℕ) (L : List γ), L.length = 2 * k → DO L →
      τF (blocks κ L) = (-1) ^ k * (-1) ^ Xc L (mpair κ)
  | 0, L, hL, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [blocks, Xc_nil, τF]
  | k + 1, [], hL, _ => by simp at hL
  | k + 1, u :: W, hL, hDO => by
    have hcu := hDO u (by simp)
    have huW : u ∈ W := by
      rw [List.count_cons_self] at hcu
      exact List.count_pos_iff.mp (by omega)
    obtain ⟨A, B, rfl⟩ := List.append_of_mem huW
    have hc2 : A.count u + B.count u = 0 := by
      simp only [List.count_cons_self, List.count_append, List.count_cons, beq_iff_eq,
        if_true] at hcu
      omega
    have hA : u ∉ A := fun h => by have := List.count_pos_iff.mpr h; omega
    have hB : u ∉ B := fun h => by have := List.count_pos_iff.mpr h; omega
    have hlen : (A ++ B).length = 2 * k := by simp at hL ⊢; omega
    have ih := τF_blocks κ hκ k (A ++ B) hlen (DO_erase_self hDO)
    set a := (κ u).1
    set b := (κ u).2
    have hab : a ≠ b := hκ u
    have hw : blocks κ (u :: (A ++ u :: B)) =
        [a, b] ++ (blocks κ A ++ a :: b :: blocks κ B) := by
      simp [blocks, List.flatMap_append, a, b]
    have h1 := τF_block_move [a, b] (blocks κ A) (blocks κ B) a b
    have h2 : τF ([a, b] ++ a :: b :: (blocks κ A ++ blocks κ B)) =
        -τF (blocks κ A ++ blocks κ B) := by
      have := τF_swap [a] (b :: (blocks κ A ++ blocks κ B)) (Ne.symm hab)
      simp only [List.singleton_append] at this
      simp only [List.cons_append, List.nil_append]
      rw [this]
      have c1 := τF_cancel [] (b :: b :: (blocks κ A ++ blocks κ B)) a
      have c2 := τF_cancel [] (blocks κ A ++ blocks κ B) b
      simp only [List.nil_append] at c1 c2
      rw [c1, c2]
    have hcount : (∀ v, A.count v ≤ 2) := by
      intro v
      by_cases hv : v ∈ u :: (A ++ u :: B)
      · have := hDO v hv
        simp only [List.count_cons, List.count_append] at this
        omega
      · have : v ∉ A := fun h => hv (by simp [h])
        rw [List.count_eq_zero_of_not_mem this]; omega
    have hpar : (-1 : ℤ) ^ ((blocks κ A).count a + (blocks κ A).count b) =
        (-1) ^ (∑ v, if A.count v = 1 then mpair κ u v else 0) := by
      rw [blocks_count, list_sum_eq_count, neg_one_pow_count_parity A _ hcount]
    rw [hw, h1, h2, ← blocks_append, ih, hpar, Xc_cons _ u A B hA hB hDO, pow_add, pow_succ]
    ring

end Crossing

end SL2W
