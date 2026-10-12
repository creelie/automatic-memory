import Mathlib

/-!
# Words: inversions, the fermionic sign, splittings
-/

open Finset

namespace SL2W

/-- All ways to write a list as `A ++ x :: B`. -/
def splits {α : Type*} : List α → List (List α × α × List α)
  | [] => []
  | a :: l => ([], a, l) :: (splits l).map (fun s => (a :: s.1, s.2.1, s.2.2))

@[simp] lemma splits_nil {α : Type*} : splits ([] : List α) = [] := rfl
@[simp] lemma splits_cons {α : Type*} (a : α) (l : List α) :
    splits (a :: l) = ([], a, l) :: (splits l).map (fun s => (a :: s.1, s.2.1, s.2.2)) := rfl

lemma splits_spec {α : Type*} : ∀ (l : List α), ∀ s ∈ splits l, s.1 ++ s.2.1 :: s.2.2 = l
  | [] => by simp
  | a :: l => by
    intro s hs
    simp only [splits_cons, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · rfl
    · simp [splits_spec l t ht]

lemma neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

section Inv

variable {β : Type*} [LinearOrder β]

/-- The number of inversions of a list. -/
def inv : List β → ℕ
  | [] => 0
  | a :: l => l.countP (fun x => x < a) + inv l

/-- The number of pairs `x ∈ X`, `y ∈ Y` with `y < x`. -/
def cross (X Y : List β) : ℕ := (X.map fun x => Y.countP (fun y => y < x)).sum

@[simp] lemma inv_nil : inv ([] : List β) = 0 := rfl
@[simp] lemma inv_cons (a : β) (l : List β) :
    inv (a :: l) = l.countP (fun x => x < a) + inv l := rfl
@[simp] lemma cross_nil (Y : List β) : cross [] Y = 0 := rfl
@[simp] lemma cross_cons (a : β) (X Y : List β) :
    cross (a :: X) Y = Y.countP (fun y => y < a) + cross X Y := by
  simp [cross]

lemma inv_append (X Y : List β) : inv (X ++ Y) = inv X + inv Y + cross X Y := by
  induction X with
  | nil => simp
  | cons a X ih => simp only [List.cons_append, inv_cons, ih, List.countP_append, cross_cons]; ring

lemma cross_cons_right (X Y : List β) (b : β) :
    cross X (b :: Y) = X.countP (fun x => b < x) + cross X Y := by
  induction X with
  | nil => simp
  | cons a X ih =>
    simp only [cross_cons, ih, List.countP_cons]
    by_cases h : b < a <;> simp [h] <;> omega

lemma countP_lt_add_countP_gt (A : List β) (i : β) :
    A.countP (fun x => x < i) + A.countP (fun x => i < x) + A.count i = A.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.countP_cons, List.count_cons, List.length_cons]
    rcases lt_trichotomy a i with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]; omega
    · simp; omega
    · simp [h, h.ne', not_lt.mpr h.le]; omega

lemma neg_one_pow_inv_split (A B : List β) (i : β) :
    (-1 : ℤ) ^ inv (i :: (A ++ i :: B)) =
      (-1) ^ (A.length + A.count i) * (-1) ^ inv (A ++ B) := by
  have h1 := countP_lt_add_countP_gt A i
  have e : inv (i :: (A ++ i :: B)) + A.count i =
      inv (A ++ B) + 2 * B.countP (fun x => x < i) + A.length := by
    simp only [inv_cons, List.countP_append, List.countP_cons, lt_irrefl, decide_false,
      inv_append, cross_cons_right]
    simp
    omega
  rw [← pow_add]
  exact neg_one_pow_congr (by omega)

open Classical in
/-- The fermionic sign of a list of colours: zero unless every colour occurs an even number
of times, and otherwise `(-1)` to the number of inversions. -/
noncomputable def τF (κ : List β) : ℤ := if ∀ c, Even (κ.count c) then (-1) ^ inv κ else 0

lemma τF_split (A B : List β) (i : β) :
    τF (i :: (A ++ i :: B)) = (-1) ^ (A.length + A.count i) * τF (A ++ B) := by
  have hc : (∀ c, Even ((i :: (A ++ i :: B)).count c)) ↔ ∀ c, Even ((A ++ B).count c) := by
    refine forall_congr' fun c => ?_
    have : (i :: (A ++ i :: B)).count c = (A ++ B).count c + 2 * (if i = c then 1 else 0) := by
      simp only [List.count_cons, List.count_append, beq_iff_eq]
      split_ifs <;> omega
    have h2 : Even (2 * (if i = c then 1 else 0)) := even_two_mul _
    rw [this, Nat.even_add]
    simp only [h2, iff_true]
  unfold τF
  rw [neg_one_pow_inv_split]
  by_cases h : ∀ c, Even ((A ++ B).count c)
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, mul_zero]

lemma sum_splits_sign (κ : List β) (i : β) :
    ((splits κ).map fun s => if s.2.1 = i then (-1 : ℤ) ^ s.1.count i else 0).sum =
      if Odd (κ.count i) then 1 else 0 := by
  induction κ with
  | nil => simp
  | cons a κ ih =>
    simp only [splits_cons, List.map_cons, List.map_map, List.sum_cons, List.count_nil,
      pow_zero]
    have : ((splits κ).map ((fun s => if s.2.1 = i then (-1 : ℤ) ^ s.1.count i else 0) ∘
        fun s => (a :: s.1, s.2.1, s.2.2))).sum =
        (if a = i then -1 else 1) *
          ((splits κ).map fun s => if s.2.1 = i then (-1 : ℤ) ^ s.1.count i else 0).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro s _
      simp only [Function.comp, List.count_cons]
      split_ifs <;> simp_all [pow_succ]
    rw [this, ih, List.count_cons]
    by_cases h : a = i
    · subst h
      by_cases ho : Odd (List.count a κ) <;> simp [ho, Nat.odd_add_one]
    · simp [h]

/-- The Wick expansion of the fermionic sign along its first letter. -/
lemma τF_wick (i : β) (κ : List β) :
    τF (i :: κ) =
      ((splits κ).map fun s => (-1) ^ s.1.length * if s.2.1 = i then τF (s.1 ++ s.2.2) else 0).sum := by
  have key : ∀ s ∈ splits κ, ((-1) ^ s.1.length * if s.2.1 = i then τF (s.1 ++ s.2.2) else 0) =
      τF (i :: κ) * (if s.2.1 = i then (-1 : ℤ) ^ s.1.count i else 0) := by
    intro s hs
    have hsp := splits_spec κ s hs
    split_ifs with h
    · rw [← hsp, h, τF_split]
      have hpow : (-1 : ℤ) ^ (s.1.length + s.1.count i) * (-1) ^ s.1.count i =
          (-1) ^ s.1.length := by
        rw [← pow_add]; exact neg_one_pow_congr (by omega)
      linear_combination (-τF (s.1 ++ s.2.2)) * hpow
    · simp
  rw [List.map_congr_left key, List.sum_map_mul_left, sum_splits_sign]
  split_ifs with h
  · simp
  · simp only [mul_zero]
    unfold τF
    rw [if_neg]
    intro h'
    have := h' i
    rw [List.count_cons_self, Nat.even_add_one] at this
    exact h (Nat.not_even_iff_odd.mp this)

lemma cross_append_right (X Y Z : List β) : cross X (Y ++ Z) = cross X Y + cross X Z := by
  induction X with
  | nil => simp
  | cons a X ih => simp only [cross_cons, List.countP_append, ih]; ring

lemma cross_perm_right (X : List β) {Y Y' : List β} (h : Y.Perm Y') : cross X Y = cross X Y' := by
  unfold cross
  congr 1
  apply List.map_congr_left
  intro x _
  exact h.countP_eq _

/-- Moving a letter to the left past a block changes the sign by the parity of the block
length plus the number of equal letters in it. -/
lemma τF_move (P A B : List β) (z : β) :
    τF (P ++ (A ++ z :: B)) = (-1) ^ (A.length + A.count z) * τF (P ++ z :: (A ++ B)) := by
  have hperm : (P ++ (A ++ z :: B)).Perm (P ++ z :: (A ++ B)) :=
    List.Perm.append_left P List.perm_middle
  have hc : (∀ c, Even ((P ++ (A ++ z :: B)).count c)) ↔
      ∀ c, Even ((P ++ z :: (A ++ B)).count c) := by
    simp only [hperm.count_eq]
  have e : inv (A ++ z :: B) + A.countP (fun x => x < z) =
      inv (z :: (A ++ B)) + A.countP (fun x => z < x) := by
    simp only [inv_append, inv_cons, cross_cons_right, List.countP_append]; ring
  have h1 := countP_lt_add_countP_gt A z
  have hcr : cross P (A ++ z :: B) = cross P (z :: (A ++ B)) :=
    cross_perm_right P List.perm_middle
  unfold τF
  by_cases h : ∀ c, Even ((P ++ z :: (A ++ B)).count c)
  · rw [if_pos (hc.mpr h), if_pos h, inv_append P (A ++ z :: B), inv_append P (z :: (A ++ B)),
      hcr, ← pow_add]
    exact neg_one_pow_congr (by omega)
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, mul_zero]

/-- Two equal adjacent letters cancel. -/
lemma τF_cancel (P S : List β) (u : β) : τF (P ++ u :: u :: S) = τF (P ++ S) := by
  have hc : (∀ c, Even ((P ++ u :: u :: S).count c)) ↔ ∀ c, Even ((P ++ S).count c) := by
    refine forall_congr' fun c => ?_
    have : (P ++ u :: u :: S).count c = (P ++ S).count c + 2 * (if u = c then 1 else 0) := by
      simp only [List.count_cons, List.count_append, beq_iff_eq]
      split_ifs <;> omega
    have h2 : Even (2 * (if u = c then 1 else 0)) := even_two_mul _
    rw [this, Nat.even_add]
    simp only [h2, iff_true]
  have e : inv (P ++ u :: u :: S) = inv (P ++ S) + 2 * S.countP (fun x => x < u) +
      2 * P.countP (fun x => u < x) := by
    simp only [inv_append, inv_cons, cross_cons_right, List.countP_cons, lt_irrefl,
      decide_false]
    simp
    ring
  unfold τF
  by_cases h : ∀ c, Even ((P ++ S).count c)
  · rw [if_pos (hc.mpr h), if_pos h, e]
    exact neg_one_pow_congr (by omega)
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

/-- Removing a pair of equal letters. -/
lemma τF_pair (P Q S : List β) (u : β) :
    τF (P ++ u :: (Q ++ u :: S)) = (-1) ^ (Q.length + Q.count u) * τF (P ++ (Q ++ S)) := by
  have h := τF_move (P ++ [u]) Q S u
  simp only [List.append_assoc, List.singleton_append] at h
  rw [h, τF_cancel]

/-- Swapping two adjacent distinct letters changes the sign. -/
lemma τF_swap (P S : List β) {a b : β} (hab : a ≠ b) :
    τF (P ++ a :: b :: S) = -τF (P ++ b :: a :: S) := by
  have h := τF_move P [a] S b
  simp only [List.singleton_append, List.length_singleton, List.count_singleton,
    beq_iff_eq] at h
  rw [h, if_neg hab]
  ring

end Inv

end SL2W
