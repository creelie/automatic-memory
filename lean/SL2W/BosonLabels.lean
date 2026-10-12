import SL2W.Labels
import SL2W.Boson

/-!
# Bosonic label words

A word of labels in which every label occurs twice is read as a product of letters `z`, `∂`
whose occurrences of each label are contracted by the symplectic form. Its value `Zb` equals
`(1/2)^m τF L · (Pol L).eval (-2)`.
-/

open Finset

namespace SL2W

section Lift

variable {α : Type*}

/-- Sum over all ways to attach a letter to every entry of a list of labels. -/
def liftSum : List α → (List (α × Fin 2) → ℚ) → ℚ
  | [], F => F []
  | u :: L, F => ∑ a : Fin 2, liftSum L (fun Z => F ((u, a) :: Z))

@[simp] lemma liftSum_nil (F : List (α × Fin 2) → ℚ) : liftSum [] F = F [] := rfl
@[simp] lemma liftSum_cons (u : α) (L : List α) (F : List (α × Fin 2) → ℚ) :
    liftSum (u :: L) F = ∑ a : Fin 2, liftSum L (fun Z => F ((u, a) :: Z)) := rfl

lemma liftSum_congr (L : List α) {F G : List (α × Fin 2) → ℚ}
    (h : ∀ Z, Z.map Prod.fst = L → F Z = G Z) : liftSum L F = liftSum L G := by
  induction L generalizing F G with
  | nil => exact h [] rfl
  | cons u L ih =>
    apply Finset.sum_congr rfl
    intro a _
    exact ih (fun Z hZ => h _ (by simp [hZ]))

lemma liftSum_mul_left (L : List α) (c : ℚ) (F : List (α × Fin 2) → ℚ) :
    liftSum L (fun Z => c * F Z) = c * liftSum L F := by
  induction L generalizing F with
  | nil => rfl
  | cons u L ih => simp [ih, Finset.mul_sum]; ring

lemma liftSum_sum {ι : Type*} (s : Finset ι) (L : List α) (F : ι → List (α × Fin 2) → ℚ) :
    liftSum L (fun Z => ∑ i ∈ s, F i Z) = ∑ i ∈ s, liftSum L (F i) := by
  induction L generalizing F with
  | nil => rfl
  | cons u L ih =>
    simp only [liftSum_cons]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact ih _

lemma liftSum_append (A B : List α) (F : List (α × Fin 2) → ℚ) :
    liftSum (A ++ B) F = liftSum A (fun ZA => liftSum B (fun ZB => F (ZA ++ ZB))) := by
  induction A generalizing F with
  | nil => rfl
  | cons u A ih => simp [ih]

lemma liftSum_map {β : Type*} (f : α → β) (L : List α) (F : List (β × Fin 2) → ℚ) :
    liftSum (L.map f) F = liftSum L (fun Z => F (Z.map fun p => (f p.1, p.2))) := by
  induction L generalizing F with
  | nil => rfl
  | cons u L ih => simp [ih]

lemma liftSum_splits (V : List α) (H : List (α × Fin 2) × (α × Fin 2) × List (α × Fin 2) → ℚ) :
    liftSum V (fun Z => ((splits Z).map H).sum) =
      ((splits V).map fun s => liftSum s.1 (fun ZA => ∑ y : Fin 2,
        liftSum s.2.2 (fun ZB => H (ZA, (s.2.1, y), ZB)))).sum := by
  induction V generalizing H with
  | nil => simp
  | cons u V ih =>
    simp only [liftSum_cons, splits_cons, List.map_cons, List.sum_cons, List.map_map]
    have : ∀ a : Fin 2, liftSum V (fun Z => H ([], (u, a), Z) +
        ((splits Z).map (H ∘ fun s => ((u, a) :: s.1, s.2.1, s.2.2))).sum) =
        liftSum V (fun Z => H ([], (u, a), Z)) +
        ((splits V).map fun s => liftSum s.1 (fun ZA => ∑ y : Fin 2,
          liftSum s.2.2 (fun ZB => H ((u, a) :: ZA, (s.2.1, y), ZB)))).sum := by
      intro a
      have h2 := liftSum_sum (Finset.univ : Finset (Fin 2)) V
        (fun i Z => if i = 0 then H ([], (u, a), Z) else
          ((splits Z).map (H ∘ fun s => ((u, a) :: s.1, s.2.1, s.2.2))).sum)
      simp only [Fin.sum_univ_two, Fin.isValue, if_true, Fin.one_eq_zero_iff,
        OfNat.ofNat_ne_one, if_false] at h2
      rw [h2, ih]
      rfl
    simp only [this, Finset.sum_add_distrib]
    congr 1
    rw [sum_list_comm]
    rfl

end Lift

section Weight

variable {α : Type*} [LinearOrder α]

/-- The pairing of the two letters of a label: `Ω(z, ∂) = 1`, `Ω(∂, z) = -1`. -/
def pairW : List (Fin 2) → ℚ
  | [a, b] => -ω a b
  | _ => 1

/-- Test the label of a lifted entry. -/
def isL (w : α) (p : α × Fin 2) : Bool := decide (p.1 = w)

/-- Rename the label of a lifted entry. -/
def relabel (v u : α) (p : α × Fin 2) : α × Fin 2 := (rename v u p.1, p.2)

lemma filter_isL_length (w : α) (Z : List (α × Fin 2)) :
    (Z.filter (isL w)).length = (Z.map Prod.fst).count w := by
  induction Z with
  | nil => rfl
  | cons p Z ih =>
    simp only [List.filter_cons, List.map_cons, List.count_cons, isL, beq_iff_eq]
    split_ifs with h1 h2 <;> simp_all

lemma filter_isL_nil {w : α} {Z : List (α × Fin 2)} (h : (Z.map Prod.fst).count w = 0) :
    Z.filter (isL w) = [] :=
  List.eq_nil_of_length_eq_zero (by rw [filter_isL_length, h])

lemma filter_relabel_other {u v w : α} (hwu : w ≠ u) (hwv : w ≠ v)
    (Z : List (α × Fin 2)) : (Z.map (relabel v u)).filter (isL w) = Z.filter (isL w) := by
  induction Z with
  | nil => rfl
  | cons p Z ih =>
    simp only [List.map_cons, List.filter_cons, ih, isL, relabel, rename]
    by_cases hp : p.1 = v
    · simp [hp, Ne.symm hwu, Ne.symm hwv]
    · simp [hp]

lemma filter_relabel_u {u v : α} (Z : List (α × Fin 2)) :
    (Z.map (relabel v u)).filter (isL u) =
      (Z.filter (fun p => isL u p || isL v p)).map (relabel v u) := by
  induction Z with
  | nil => rfl
  | cons p Z ih =>
    simp only [List.map_cons, List.filter_cons, ih, isL, relabel, rename]
    by_cases hp : p.1 = v
    · simp [hp, relabel, rename]
    · by_cases hpu : p.1 = u
      · simp [hp, hpu, relabel, rename]
      · simp [hp, hpu]

lemma filter_isL_sub_u (u v : α) (Z : List (α × Fin 2)) :
    (Z.filter (fun p => isL u p || isL v p)).filter (isL u) = Z.filter (isL u) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro p _
  cases isL u p <;> cases isL v p <;> rfl

lemma filter_isL_sub_v (u v : α) (Z : List (α × Fin 2)) :
    (Z.filter (fun p => isL u p || isL v p)).filter (isL v) = Z.filter (isL v) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro p _
  cases isL u p <;> cases isL v p <;> rfl

lemma map_fst_filter_uv (u v : α) (Z : List (α × Fin 2)) :
    (Z.filter (fun p => isL u p || isL v p)).map Prod.fst =
      (Z.map Prod.fst).filter (fun x => x = u ∨ x = v) := by
  induction Z with
  | nil => rfl
  | cons p Z ih =>
    by_cases h : p.1 = u ∨ p.1 = v
    · have h' : (isL u p || isL v p) = true := by simpa [isL] using h
      rw [List.filter_cons_of_pos (p := fun q => isL u q || isL v q) (a := p) h',
        List.map_cons, List.map_cons,
        List.filter_cons_of_pos (p := fun x => decide (x = u ∨ x = v)) (by simpa using h), ih]
    · have h' : (isL u p || isL v p) = false := by simpa [isL] using h
      rw [List.filter_cons_of_neg (p := fun q => isL u q || isL v q) (a := p) (by simp [h']),
        List.map_cons,
        List.filter_cons_of_neg (p := fun x => decide (x = u ∨ x = v)) (by simpa using h), ih]

lemma count_add_count_of_forall {u v : α} (huv : u ≠ v) (l : List α)
    (hm : ∀ x ∈ l, x = u ∨ x = v) : l.count u + l.count v = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.count_cons, beq_iff_eq, List.length_cons]
    have := ih (fun y hy => hm y (List.mem_cons_of_mem x hy))
    rcases hm x List.mem_cons_self with h | h
    · subst h; simp [huv]; omega
    · subst h; simp [Ne.symm huv]; omega

/-- The two lifted entries carrying the labels `u` and `v`. -/
lemma filter_uv_pair {u v : α} (huv : u ≠ v) (Z : List (α × Fin 2))
    (hu : (Z.map Prod.fst).count u = 1) (hv : (Z.map Prod.fst).count v = 1) :
    ∃ cu cv : Fin 2, Z.filter (isL u) = [(u, cu)] ∧ Z.filter (isL v) = [(v, cv)] ∧
      ((Z.map Prod.fst).filter (fun x => x = u ∨ x = v) = [u, v] ∧
          Z.filter (fun p => isL u p || isL v p) = [(u, cu), (v, cv)] ∨
        (Z.map Prod.fst).filter (fun x => x = u ∨ x = v) = [v, u] ∧
          Z.filter (fun p => isL u p || isL v p) = [(v, cv), (u, cu)]) := by
  set Zf := Z.filter (fun p => isL u p || isL v p) with hZf
  have hlu : (Zf.filter (isL u)).length = 1 := by
    rw [filter_isL_sub_u, filter_isL_length, hu]
  have hlv : (Zf.filter (isL v)).length = 1 := by
    rw [filter_isL_sub_v, filter_isL_length, hv]
  have hmem : ∀ q ∈ Zf, q.1 = u ∨ q.1 = v := by
    intro q hq
    rw [hZf, List.mem_filter] at hq
    simpa [isL] using hq.2
  have hlen : Zf.length = 2 := by
    have h1 := filter_isL_length u Zf
    have h2 := filter_isL_length v Zf
    have := count_add_count_of_forall huv (Zf.map Prod.fst) (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hmem q hq)
    rw [List.length_map] at this
    omega
  obtain ⟨q1, q2, hq⟩ := List.length_eq_two.mp hlen
  have hq1 := hmem q1 (by rw [hq]; simp)
  have hq2 := hmem q2 (by rw [hq]; simp)
  have hRf : (Z.map Prod.fst).filter (fun x => x = u ∨ x = v) = [q1.1, q2.1] := by
    rw [← map_fst_filter_uv, ← hZf, hq]; rfl
  have hfu : Z.filter (isL u) = Zf.filter (isL u) := (filter_isL_sub_u u v Z).symm
  have hfv : Z.filter (isL v) = Zf.filter (isL v) := (filter_isL_sub_v u v Z).symm
  rw [hq] at hlu hlv hfu hfv
  rcases q1 with ⟨r1, c1⟩
  rcases q2 with ⟨r2, c2⟩
  simp only at hq1 hq2 hRf
  rcases hq1 with rfl | rfl <;> rcases hq2 with rfl | rfl
  · simp [List.filter_cons, isL] at hlu
  · refine ⟨c1, c2, ?_, ?_, Or.inl ⟨hRf, hq⟩⟩
    · rw [hfu]; simp [List.filter_cons, isL, Ne.symm huv]
    · rw [hfv]; simp [List.filter_cons, isL, huv]
  · refine ⟨c2, c1, ?_, ?_, Or.inr ⟨hRf, hq⟩⟩
    · rw [hfu]; simp [List.filter_cons, isL, huv, Ne.symm huv]
    · rw [hfv]; simp [List.filter_cons, isL, huv, Ne.symm huv]
  · simp [List.filter_cons, isL] at hlv

end Weight

section Zb

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The weight of a lifted word: the product over the labels of the pairing of their letters. -/
noncomputable def wt (Z : List (α × Fin 2)) : ℚ :=
  ∏ w : α, pairW ((Z.filter (isL w)).map Prod.snd)

/-- The bosonic value of a word of labels. -/
noncomputable def Zb (L : List α) : ℚ := liftSum L (fun Z => wt Z * τb (Z.map Prod.snd))

lemma wt_split1 (u : α) (Z : List (α × Fin 2)) :
    wt Z = pairW ((Z.filter (isL u)).map Prod.snd) *
      ∏ w ∈ univ.erase u, pairW ((Z.filter (isL w)).map Prod.snd) := by
  unfold wt; exact (Finset.mul_prod_erase univ _ (mem_univ u)).symm

lemma wt_split2 {u v : α} (huv : u ≠ v) (Z : List (α × Fin 2)) :
    wt Z = pairW ((Z.filter (isL u)).map Prod.snd) *
      (pairW ((Z.filter (isL v)).map Prod.snd) *
        ∏ w ∈ (univ.erase u).erase v, pairW ((Z.filter (isL w)).map Prod.snd)) := by
  unfold wt
  have h1 := Finset.mul_prod_erase (univ.erase u)
    (fun w => pairW ((Z.filter (isL w)).map Prod.snd)) (show v ∈ univ.erase u by simp [Ne.symm huv])
  have h2 := Finset.mul_prod_erase univ
    (fun w => pairW ((Z.filter (isL w)).map Prod.snd)) (mem_univ u)
  rw [h1, h2]

lemma pairW_swap (a b : Fin 2) : pairW [b, a] = -pairW [a, b] := by
  fin_cases a <;> fin_cases b <;> simp [pairW, ω]

lemma letter_sum_self (R : ℚ) : ∑ a : Fin 2, ∑ y : Fin 2, ω a y * (pairW [a, y] * R) = -2 * R := by
  simp [Fin.sum_univ_two, pairW, ω]; ring

lemma letter_sum_A (cu cv : Fin 2) (R : ℚ) :
    ∑ a : Fin 2, ∑ y : Fin 2, ω a y * (pairW [a, cu] * (pairW [cv, y] * R)) =
      pairW [cu, cv] * R := by
  fin_cases cu <;> fin_cases cv <;> simp [Fin.sum_univ_two, pairW, ω]

lemma letter_sum_B (cu cv : Fin 2) (R : ℚ) :
    ∑ a : Fin 2, ∑ y : Fin 2, ω a y * (pairW [a, cu] * (pairW [y, cv] * R)) =
      -(pairW [cu, cv] * R) := by
  fin_cases cu <;> fin_cases cv <;> simp [Fin.sum_univ_two, pairW, ω]

lemma neg_one_pow_mul_self_q (n : ℕ) : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- Contracting the first letter with the letter at a split. -/
lemma bracket (u v : α) (A B : List α) (hDO : DO (u :: (A ++ v :: B)))
    (ZA ZB : List (α × Fin 2)) (hA : ZA.map Prod.fst = A) (hB : ZB.map Prod.fst = B) :
    ∑ a : Fin 2, ∑ y : Fin 2, ω a y * wt ((u, a) :: (ZA ++ (v, y) :: ZB)) =
      ((if v = u then -2 else 1) * (τF (u :: (A ++ v :: B)) : ℚ) * (-1) ^ A.length *
        (τF ((A ++ B).map (rename v u)) : ℚ)) * wt ((ZA ++ ZB).map (relabel v u)) := by
  by_cases hvu : v = u
  · subst hvu
    have hc := hDO v (by simp)
    simp only [List.count_cons_self, List.count_append] at hc
    have hA0 : A.count v = 0 := by omega
    have hB0 : B.count v = 0 := by omega
    rw [map_rename_self]
    have hrel : (ZA ++ ZB).map (relabel v v) = ZA ++ ZB := by
      rw [List.map_congr_left (g := id) (fun p _ => by simp [relabel, rename_self]), List.map_id]
    rw [hrel]
    have hZA : ZA.filter (isL v) = [] := filter_isL_nil (by rw [hA]; exact hA0)
    have hZB : ZB.filter (isL v) = [] := filter_isL_nil (by rw [hB]; exact hB0)
    have e1 : ∀ a y : Fin 2, wt ((v, a) :: (ZA ++ (v, y) :: ZB)) = pairW [a, y] *
        ∏ w ∈ univ.erase v, pairW (((ZA ++ ZB).filter (isL w)).map Prod.snd) := by
      intro a y
      rw [wt_split1 v]
      congr 1
      · simp [List.filter_cons, List.filter_append, hZA, hZB, isL]
      · apply Finset.prod_congr rfl
        intro w hw
        have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
        simp [List.filter_cons, List.filter_append, isL, Ne.symm hwv]
    have e2 : wt (ZA ++ ZB) =
        ∏ w ∈ univ.erase v, pairW (((ZA ++ ZB).filter (isL w)).map Prod.snd) := by
      rw [wt_split1 v]
      simp [List.filter_append, hZA, hZB, pairW]
    simp only [e1, e2, if_true]
    rw [letter_sum_self, τF_split]
    have hsq : (τF (A ++ B) : ℚ) * τF (A ++ B) = 1 := by
      exact_mod_cast τF_DO_sq (DO_erase_self hDO)
    have hp := neg_one_pow_mul_self_q A.length
    rw [hA0, add_zero]
    push_cast
    linear_combination (2 * (τF (A ++ B) : ℚ) * τF (A ++ B) *
      ∏ w ∈ univ.erase v, pairW (((ZA ++ ZB).filter (isL w)).map Prod.snd)) * hp +
      (2 * ∏ w ∈ univ.erase v, pairW (((ZA ++ ZB).filter (isL w)).map Prod.snd)) * hsq
  · have huv : u ≠ v := Ne.symm hvu
    have hcu := hDO u (by simp)
    have hcv := hDO v (by simp)
    simp only [List.count_cons_self, List.count_append, List.count_cons, beq_iff_eq, hvu,
      huv, if_false] at hcu hcv
    set Z0 := ZA ++ ZB with hZ0
    have hZ0f : Z0.map Prod.fst = A ++ B := by simp [hZ0, hA, hB]
    have hu0 : (Z0.map Prod.fst).count u = 1 := by rw [hZ0f, List.count_append]; omega
    have hv0 : (Z0.map Prod.fst).count v = 1 := by rw [hZ0f, List.count_append]; omega
    obtain ⟨cu, cv, hfu, hfv, hord⟩ := filter_uv_pair huv Z0 hu0 hv0
    have hrest : ∀ w ∈ (univ.erase u).erase v, ∀ a y : Fin 2,
        ((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL w) = Z0.filter (isL w) := by
      intro w hw a y
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
      simp [hZ0, List.filter_cons, List.filter_append, isL, Ne.symm hwv, Ne.symm hwu]
    have hrestc : ∀ w ∈ (univ.erase u).erase v,
        (Z0.map (relabel v u)).filter (isL w) = Z0.filter (isL w) := by
      intro w hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
      exact filter_relabel_other hwu hwv Z0
    set REST := ∏ w ∈ (univ.erase u).erase v, pairW ((Z0.filter (isL w)).map Prod.snd)
      with hREST
    have hZ1u : ∀ a y : Fin 2, (((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL u)).map Prod.snd =
        [a, cu] := by
      intro a y
      have : ((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL u) = (u, a) :: Z0.filter (isL u) := by
        simp [hZ0, List.filter_cons, List.filter_append, isL, hvu]
      rw [this, hfu]; rfl
    have hZcv : (Z0.map (relabel v u)).filter (isL v) = [] := by
      apply filter_isL_nil
      rw [List.map_map]
      have : (Prod.fst ∘ relabel v u) = rename v u ∘ Prod.fst := by
        funext p; rfl
      rw [this, ← List.map_map, hZ0f, count_map_rename hvu]
      simp [hvu]
    have hτ : (τF (u :: (A ++ v :: B)) : ℚ) * (-1) ^ A.length *
        (τF ((A ++ B).map (rename v u)) : ℚ) =
        (-1) ^ A.count v *
          (if (A ++ B).filter (fun x => x = u ∨ x = v) = [u, v] then -1 else 1) := by
      have hm := τF_move [u] A B v
      simp only [List.singleton_append] at hm
      have hh := τF_head_pair (A ++ B) huv (by rw [List.count_append]; omega)
        (by rw [List.count_append]; omega)
      rw [hm, hh]
      have hsq : (τF ((A ++ B).map (rename v u)) : ℚ) * τF ((A ++ B).map (rename v u)) = 1 := by
        exact_mod_cast τF_DO_sq (DO_contract hDO hvu)
      have hp := neg_one_pow_mul_self_q A.length
      push_cast
      rw [pow_add]
      split_ifs
      · linear_combination (-(-1 : ℚ) ^ A.count v * (-1) ^ A.length * (-1) ^ A.length) * hsq -
          (-1 : ℚ) ^ A.count v * hp
      · linear_combination ((-1 : ℚ) ^ A.count v * (-1) ^ A.length * (-1) ^ A.length) * hsq +
          (-1 : ℚ) ^ A.count v * hp
    simp only [if_neg hvu, one_mul]
    rw [hτ]
    have hvZ : ZA.filter (isL v) ++ ZB.filter (isL v) = [(v, cv)] := by
      rw [← List.filter_append]; exact hfv
    have hlA : (ZA.filter (isL v)).length = A.count v := by rw [filter_isL_length, hA]
    have hRf : (A ++ B).filter (fun x => x = u ∨ x = v) = [u, v] ∨
        (A ++ B).filter (fun x => x = u ∨ x = v) = [v, u] := by
      rw [← hZ0f]; rcases hord with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hcu' : ((Z0.map (relabel v u)).filter (isL u)).map Prod.snd =
        if (A ++ B).filter (fun x => x = u ∨ x = v) = [u, v] then [cu, cv] else [cv, cu] := by
      rw [filter_relabel_u, ← hZ0f]
      rcases hord with h | h
      · rw [h.2, if_pos h.1]; rfl
      · have hne : (Z0.map Prod.fst).filter (fun x => x = u ∨ x = v) ≠ [u, v] := by
          rw [h.1]; simp [huv]
        rw [h.2, if_neg hne]; rfl
    have hRc : ∏ w ∈ (univ.erase u).erase v,
        pairW (((Z0.map (relabel v u)).filter (isL w)).map Prod.snd) = REST := by
      apply Finset.prod_congr rfl
      intro w hw; rw [hrestc w hw]
    have hR1 : ∀ a y : Fin 2, ∏ w ∈ (univ.erase u).erase v,
        pairW ((((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL w)).map Prod.snd) = REST := by
      intro a y
      apply Finset.prod_congr rfl
      intro w hw; rw [hrest w hw a y]
    rw [wt_split2 huv (Z0.map (relabel v u)), hcu', hZcv, hRc]
    simp only [wt_split2 huv, hZ1u, hR1]
    have hcA : A.count v ≤ 1 := by omega
    have hnil : pairW (List.map Prod.snd ([] : List (α × Fin 2))) = 1 := rfl
    rw [hnil, one_mul]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcA with h0 | h1
    · have hZA : ZA.filter (isL v) = [] := List.eq_nil_of_length_eq_zero (by rw [hlA, h0])
      rw [hZA, List.nil_append] at hvZ
      have e : ∀ a y : Fin 2, (((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL v)).map
          Prod.snd = [y, cv] := by
        intro a y
        simp [List.filter_cons, List.filter_append, isL, hvu, huv, hZA, hvZ]
      simp only [e, letter_sum_B]
      rw [h0, pow_zero, one_mul]
      rcases hRf with h | h
      · rw [if_pos h, if_pos h]; ring
      · have hne : (A ++ B).filter (fun x => x = u ∨ x = v) ≠ [u, v] := by rw [h]; simp [huv]
        rw [if_neg hne, if_neg hne, pairW_swap]; ring
    · have hZB : ZB.filter (isL v) = [] := by
        have := congrArg List.length hvZ
        rw [List.length_append, hlA, h1] at this
        exact List.eq_nil_of_length_eq_zero (by simpa using this)
      rw [hZB, List.append_nil] at hvZ
      have e : ∀ a y : Fin 2, (((u, a) :: (ZA ++ (v, y) :: ZB)).filter (isL v)).map
          Prod.snd = [cv, y] := by
        intro a y
        simp [List.filter_cons, List.filter_append, isL, hvu, huv, hZB, hvZ]
      simp only [e, letter_sum_A]
      rw [h1, pow_one]
      rcases hRf with h | h
      · rw [if_pos h, if_pos h]; ring
      · have hne : (A ++ B).filter (fun x => x = u ∨ x = v) ≠ [u, v] := by rw [h]; simp [huv]
        rw [if_neg hne, if_neg hne, pairW_swap]; ring

lemma map_snd_relabel (v u : α) (Z : List (α × Fin 2)) :
    (Z.map (relabel v u)).map Prod.snd = Z.map Prod.snd := by
  induction Z with
  | nil => rfl
  | cons p Z ih => simp [relabel, ih]

/-- The recursion for the bosonic value along the first label. -/
lemma Zb_cons (u : α) (V : List α) (hDO : DO (u :: V)) :
    Zb (u :: V) = ((splits V).map fun s => (1 / 2 : ℚ) *
      ((if s.2.1 = u then -2 else 1) * (τF (u :: V) : ℚ) * (-1) ^ s.1.length *
        (τF ((s.1 ++ s.2.2).map (rename s.2.1 u)) : ℚ)) *
      Zb ((s.1 ++ s.2.2).map (rename s.2.1 u))).sum := by
  unfold Zb
  rw [liftSum_cons]
  have step1 : ∀ a : Fin 2,
      liftSum V (fun Z => wt ((u, a) :: Z) * τb (((u, a) :: Z).map Prod.snd)) =
      liftSum V (fun Z => ((splits Z).map fun s => (1 / 2 : ℚ) * (ω a s.2.1.2 *
        wt ((u, a) :: (s.1 ++ s.2.1 :: s.2.2)) * τb ((s.1 ++ s.2.2).map Prod.snd))).sum) := by
    intro a
    apply liftSum_congr
    intro Z _
    rw [List.map_cons, τb_wick, splits_map, List.map_map, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro s hs
    rw [← splits_spec Z s hs]
    simp only [Function.comp_apply, List.map_append]
    ring
  rw [Finset.sum_congr rfl (fun a _ => step1 a)]
  simp only [liftSum_splits]
  rw [sum_list_comm]
  congr 1
  apply List.map_congr_left
  rintro ⟨A, v, B⟩ hs
  have hV : A ++ v :: B = V := splits_spec V _ hs
  simp only
  subst hV
  have L1 : (∑ a : Fin 2, liftSum A (fun ZA => ∑ y : Fin 2, liftSum B (fun ZB =>
      (1 / 2 : ℚ) * (ω a y * wt ((u, a) :: (ZA ++ (v, y) :: ZB)) *
        τb ((ZA ++ ZB).map Prod.snd))))) =
      liftSum A (fun ZA => liftSum B (fun ZB => ∑ a : Fin 2, ∑ y : Fin 2,
        (1 / 2 : ℚ) * (ω a y * wt ((u, a) :: (ZA ++ (v, y) :: ZB)) *
          τb ((ZA ++ ZB).map Prod.snd)))) := by
    simp only [liftSum_sum]
  rw [L1, liftSum_map, liftSum_append, ← liftSum_mul_left]
  apply liftSum_congr
  intro ZA hZA
  rw [← liftSum_mul_left]
  apply liftSum_congr
  intro ZB hZB
  have hb := bracket u v A B hDO ZA ZB hZA hZB
  have e : ∀ a y : Fin 2, (1 / 2 : ℚ) * (ω a y * wt ((u, a) :: (ZA ++ (v, y) :: ZB)) *
      τb ((ZA ++ ZB).map Prod.snd)) = ((1 / 2 : ℚ) * τb ((ZA ++ ZB).map Prod.snd)) *
        (ω a y * wt ((u, a) :: (ZA ++ (v, y) :: ZB))) := by
    intro a y; ring
  simp only [e, ← Finset.mul_sum, hb]
  show _ = _ * (wt ((ZA ++ ZB).map (relabel v u)) *
    τb (((ZA ++ ZB).map (relabel v u)).map Prod.snd))
  rw [map_snd_relabel]
  ring

lemma Zb_nil : Zb ([] : List α) = 1 := by
  have h1 : τb [] = 1 := by
    unfold τb Pdiag
    simp only [chg_nil, if_true, Pw_nil]
    rw [← Polynomial.C_1, ell_C]
  simp [Zb, wt, pairW, h1]

/-- The closed form of the bosonic value of a word in which every label occurs twice. -/
theorem Zb_eq : ∀ (m : ℕ) (L : List α), L.length = 2 * m → DO L →
    Zb L = (1 / 2 : ℚ) ^ m * (τF L : ℚ) * (Pol L).eval (-2)
  | 0, L, hL, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [Zb_nil, τF]
  | m + 1, [], hL, _ => by simp at hL
  | m + 1, u :: W, hL, hDO => by
    have hW : ∀ s ∈ splits W, (s.1 ++ s.2.2).length = 2 * m := by
      intro s hs
      have := length_of_mem_splits hs
      simp at hL ⊢; omega
    rw [Zb_cons u W hDO, Pol_cons, Polynomial.eval_listSum, List.map_map,
      ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro s hs
    have hsp := splits_spec W s hs
    have hDO' := hDO
    rw [← hsp] at hDO'
    have hDOC : DO ((s.1 ++ s.2.2).map (rename s.2.1 u)) := by
      by_cases hx : s.2.1 = u
      · rw [hx, map_rename_self]; rw [hx] at hDO'; exact DO_erase_self hDO'
      · exact DO_contract hDO' hx
    have hCl : ((s.1 ++ s.2.2).map (rename s.2.1 u)).length = 2 * m := by
      rw [List.length_map]; exact hW s hs
    rw [Zb_eq m _ hCl hDOC]
    have hsq : (τF ((s.1 ++ s.2.2).map (rename s.2.1 u)) : ℚ) *
        τF ((s.1 ++ s.2.2).map (rename s.2.1 u)) = 1 := by
      exact_mod_cast τF_DO_sq hDOC
    simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one]
    by_cases hx : s.2.1 = u
    · simp only [hx, if_true, Polynomial.eval_X]
      rw [hx] at hsq
      linear_combination (-(1 / 2 : ℚ) ^ (m + 1) * 2 * (τF (u :: W) : ℚ) * (-1) ^ s.1.length *
        (Pol ((s.1 ++ s.2.2).map (rename u u))).eval (-2)) * hsq
    · simp only [hx, if_false, Polynomial.eval_one, mul_one]
      linear_combination ((1 / 2 : ℚ) ^ (m + 1) * (τF (u :: W) : ℚ) * (-1) ^ s.1.length *
        (Pol ((s.1 ++ s.2.2).map (rename s.2.1 u))).eval (-2)) * hsq

end Zb

end SL2W
