import SL2W.Defs

/-!
# The graph invariant `ξ` satisfies the four-term relations

Each `T k` satisfies `T k G - T k G'_{ab} = T k G̃_{ab} - T k G̃'_{ab}`: both sides are twice the
signed number of admissible assignments with `|p a ∩ p b| = 1`, and replacing `p b` by
`p a ∆ p b` matches the two sums term by term.
-/

open Finset
open scoped symmDiff

namespace SL2W

section FourT

open Classical

variable {V : Type} [Fintype V]

/-- The sign of an edge under an assignment of subsets. -/
noncomputable def sgnE {k : ℕ} (p : V → Finset (Fin k)) (e : Sym2 V) : ℤ :=
  (-1) ^ (Sym2.lift ⟨fun a b => (p a ∩ p b).card, fun a b => by simp only [inter_comm]⟩ e)

omit [Fintype V] in
lemma sgnE_mk {k : ℕ} (p : V → Finset (Fin k)) (x y : V) :
    sgnE p s(x, y) = (-1) ^ (p x ∩ p y).card := rfl

omit [Fintype V] in
lemma sgnE_sq {k : ℕ} (p : V → Finset (Fin k)) (e : Sym2 V) : sgnE p e * sgnE p e = 1 := by
  unfold sgnE
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The edges of a graph as a finset. -/
noncomputable def Ed (G : SimpleGraph V) : Finset (Sym2 V) := univ.filter (· ∈ G.edgeSet)

lemma edgeSign_eq (G : SimpleGraph V) {k : ℕ} (p : V → Finset (Fin k)) :
    edgeSign G p = ∏ e ∈ Ed G, sgnE p e := by
  unfold edgeSign
  apply Finset.prod_congr
  · ext e; simp [Ed, SimpleGraph.mem_edgeFinset]
  · intro e _; rfl

lemma prod_symmDiff_sq {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℤ) (hf : ∀ x, f x * f x = 1)
    (S S' : Finset α) : ∏ x ∈ S', f x = (∏ x ∈ S, f x) * ∏ x ∈ S ∆ S', f x := by
  have h : ∀ T : Finset α, ∏ x ∈ T, f x = ∏ x, if x ∈ T then f x else 1 := by
    intro T; rw [Finset.prod_ite_mem, univ_inter]
  rw [h S', h S, h (S ∆ S'), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  have := hf x
  by_cases h1 : x ∈ S <;> by_cases h2 : x ∈ S' <;> simp [mem_symmDiff, h1, h2, this]

lemma edgeSign_symmDiff (G H : SimpleGraph V) {k : ℕ} (p : V → Finset (Fin k)) :
    edgeSign H p = edgeSign G p * ∏ e ∈ Ed G ∆ Ed H, sgnE p e := by
  rw [edgeSign_eq, edgeSign_eq]
  exact prod_symmDiff_sq _ (sgnE_sq p) _ _

lemma Ed_toggle (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    Ed (toggle G a b) = Ed G ∆ {s(a, b)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Ed, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet, mem_symmDiff,
      mem_singleton, Sym2.eq_iff]
    simp only [toggle, xor_def]
    have h1 : G.Adj x y → x ≠ y := G.ne_of_adj
    by_cases hxy : x = y
    · subst hxy
      have : ¬ (x = a ∧ x = b) := fun h => hab (h.1.symm.trans h.2)
      have : ¬ (x = b ∧ x = a) := fun h => hab (h.2.symm.trans h.1)
      simp_all
    · tauto

/-- The neighbours of `b` other than `a`. -/
noncomputable def Nb (G : SimpleGraph V) (a b : V) : Finset V :=
  univ.filter fun y => y ≠ a ∧ y ≠ b ∧ G.Adj b y

lemma Ed_tilde (G : SimpleGraph V) (a b : V) :
    Ed (tilde G a b) = Ed G ∆ (Nb G a b).image (fun y => s(a, y)) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Ed, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet, mem_symmDiff,
      mem_image, Nb, Sym2.eq_iff]
    simp only [tilde, xor_def]
    have h1 : G.Adj x y → x ≠ y := G.ne_of_adj
    have h2 : G.Adj b y → b ≠ y := G.ne_of_adj
    have h3 : G.Adj b x → b ≠ x := G.ne_of_adj
    by_cases hxy : x = y
    · subst hxy
      constructor
      · intro h; exact absurd rfl h.1
      · rintro (⟨h, _⟩ | ⟨⟨z, ⟨hza, _, _⟩, h⟩, _⟩)
        · exact absurd h (G.irrefl)
        · exfalso
          rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
          · exact hza (h'.trans h.symm)
          · exact hza (h'.trans h.symm)
    · constructor
      · rintro ⟨_, h⟩
        rcases h with ⟨hA, hC⟩ | ⟨hC, hA⟩
        · left
          refine ⟨hA, ?_⟩
          rintro ⟨z, ⟨hza, hzb, hbz⟩, h⟩
          apply hC
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, hzb, hbz⟩
          · exact Or.inr ⟨rfl, hzb, hbz⟩
        · right
          refine ⟨?_, hA⟩
          rcases hC with ⟨rfl, hyb, hby⟩ | ⟨rfl, hxb, hbx⟩
          · exact ⟨y, ⟨fun e => hxy e.symm, hyb, hby⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨x, ⟨hxy, hxb, hbx⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rintro (⟨hA, hC⟩ | ⟨⟨z, ⟨hza, hzb, hbz⟩, h⟩, hA⟩)
        · refine ⟨hxy, Or.inl ⟨hA, ?_⟩⟩
          rintro (⟨rfl, hyb, hby⟩ | ⟨rfl, hxb, hbx⟩)
          · exact hC ⟨y, ⟨fun e => hxy e.symm, hyb, hby⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact hC ⟨x, ⟨hxy, hxb, hbx⟩, Or.inr ⟨rfl, rfl⟩⟩
        · refine ⟨hxy, Or.inr ⟨?_, hA⟩⟩
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, hzb, hbz⟩
          · exact Or.inr ⟨rfl, hzb, hbz⟩

lemma edgeSign_toggle (G : SimpleGraph V) {a b : V} (hab : a ≠ b) {k : ℕ}
    (p : V → Finset (Fin k)) : edgeSign (toggle G a b) p = edgeSign G p * sgnE p s(a, b) := by
  rw [edgeSign_symmDiff G, Ed_toggle G hab, symmDiff_symmDiff_cancel_left, prod_singleton]

lemma edgeSign_tilde (G : SimpleGraph V) (a b : V) {k : ℕ} (p : V → Finset (Fin k)) :
    edgeSign (tilde G a b) p = edgeSign G p * ∏ y ∈ Nb G a b, sgnE p s(a, y) := by
  rw [edgeSign_symmDiff G, Ed_tilde, symmDiff_symmDiff_cancel_left, prod_image]
  intro y hy z _ h
  simp only [Nb, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
  rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨_, h2⟩
  · exact h
  · exact absurd h2 hy.1

omit [Fintype V] in
lemma card_symmDiff_add {α : Type*} [DecidableEq α] (X Y : Finset α) :
    (X ∆ Y).card + 2 * (X ∩ Y).card = X.card + Y.card := by
  have h1 : (X ∆ Y) ∪ (X ∩ Y) = X ∪ Y := by
    ext z; simp only [mem_union, mem_symmDiff, mem_inter]; tauto
  have h2 : Disjoint (X ∆ Y) (X ∩ Y) := by
    rw [disjoint_left]; intro z; simp only [mem_symmDiff, mem_inter]; tauto
  have h3 := card_union_of_disjoint h2
  rw [h1] at h3
  have h4 := card_union_add_card_inter X Y
  omega

omit [Fintype V] in
lemma neg_one_pow_symmDiff_inter {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (-1 : ℤ) ^ ((A ∆ B) ∩ C).card = (-1) ^ (A ∩ C).card * (-1) ^ (B ∩ C).card := by
  have e : (A ∆ B) ∩ C = (A ∩ C) ∆ (B ∩ C) := inf_symmDiff_distrib_right A B C
  rw [e, ← pow_add, ← card_symmDiff_add (A ∩ C) (B ∩ C), pow_add, pow_mul]
  norm_num

/-- Replacing `p b` by `p a ∆ p b`. -/
noncomputable def flip4 {k : ℕ} (a b : V) (p : V → Finset (Fin k)) : V → Finset (Fin k) :=
  Function.update p b (p a ∆ p b)

lemma edgeSign_flip4 (G : SimpleGraph V) {a b : V} (hab : a ≠ b) {k : ℕ}
    (p : V → Finset (Fin k)) (ha : Even (p a).card) :
    edgeSign G (flip4 a b p) = edgeSign G p * ∏ y ∈ Nb G a b, sgnE p s(a, y) := by
  set q := flip4 a b p with hqdef
  have hq : ∀ v, v ≠ b → q v = p v := fun v hv => Function.update_of_ne hv _ _
  have hqb : q b = p a ∆ p b := Function.update_self _ _ _
  have hqa : q a = p a := hq a hab
  have key : ∀ e, sgnE q e = sgnE p e * (sgnE q e * sgnE p e) := by
    intro e; rw [mul_comm (sgnE q e), ← mul_assoc, sgnE_sq, one_mul]
  have hab' : ∀ x y, s(x, y) = s(b, a) → sgnE q s(x, y) * sgnE p s(x, y) = 1 := by
    intro x y hxy
    rw [hxy, sgnE_mk, sgnE_mk, hqb, hqa, neg_one_pow_symmDiff_inter, inter_self,
      Even.neg_one_pow ha, one_mul, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [edgeSign_eq, edgeSign_eq, Finset.prod_congr rfl (fun e _ => key e), Finset.prod_mul_distrib]
  congr 1
  have hsub : (Nb G a b).image (fun y => s(b, y)) ⊆ Ed G := by
    intro e he
    simp only [mem_image, Nb, mem_filter, mem_univ, true_and] at he
    obtain ⟨y, ⟨_, _, hby⟩, rfl⟩ := he
    simp [Ed, hby]
  rw [← Finset.prod_subset hsub, prod_image]
  · apply Finset.prod_congr rfl
    intro y hy
    simp only [Nb, mem_filter, mem_univ, true_and] at hy
    rw [sgnE_mk, sgnE_mk, sgnE_mk, hqb, hq y hy.2.1, neg_one_pow_symmDiff_inter, mul_assoc,
      ← pow_add, ← two_mul, pow_mul]
    norm_num
  · intro y hy z _ h
    simp only [Nb, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd h2 hy.2.1
  · intro e he hne
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Ed, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet] at he
      have hxy : x ≠ y := G.ne_of_adj he
      by_cases hx : x = b
      · subst hx
        by_cases hy : y = a
        · subst hy; exact hab' _ _ rfl
        · exact absurd (mem_image.mpr ⟨y, by simp [Nb, hy, Ne.symm hxy, he], rfl⟩) hne
      · by_cases hy : y = b
        · subst hy
          by_cases hxa : x = a
          · subst hxa; exact hab' _ _ Sym2.eq_swap
          · exact absurd (mem_image.mpr ⟨x, by simp [Nb, hxa, hx, he.symm], Sym2.eq_swap⟩) hne
        · rw [sgnE_mk, sgnE_mk, hq x hx, hq y hy, ← pow_add, ← two_mul, pow_mul]
          norm_num

/-- The admissible assignments with `|p a ∩ p b| = 1`. -/
noncomputable def S4 (k : ℕ) (a b : V) : Finset (V → Finset (Fin k)) :=
  univ.filter fun p => ((∀ v, (p v).card = 2) ∧ univ.biUnion p = univ) ∧ (p a ∩ p b).card = 1

lemma T_sub_toggle (H : SimpleGraph V) {a b : V} (hab : a ≠ b) (k : ℕ) :
    T k H - T k (toggle H a b) = 2 * ∑ p ∈ S4 k a b, edgeSign H p := by
  unfold T S4
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [edgeSign_toggle H hab, sgnE_mk]
  by_cases hv : (∀ v, (p v).card = 2) ∧ univ.biUnion p = univ
  · rw [if_pos hv, if_pos hv]
    by_cases h1 : (p a ∩ p b).card = 1
    · rw [if_pos ⟨hv, h1⟩, h1]; ring
    · rw [if_neg (fun h => h1 h.2)]
      have hle : (p a ∩ p b).card ≤ 2 := (hv.1 a) ▸ card_le_card inter_subset_left
      have he : Even (p a ∩ p b).card := by
        rcases (show (p a ∩ p b).card = 0 ∨ (p a ∩ p b).card = 2 by omega) with h | h <;>
          rw [h] <;> decide
      rw [Even.neg_one_pow he]; ring
  · rw [if_neg hv, if_neg hv, if_neg (fun h => hv h.1)]; ring

lemma flip4_mem {k : ℕ} {a b : V} (hab : a ≠ b) {p : V → Finset (Fin k)} (hp : p ∈ S4 k a b) :
    flip4 a b p ∈ S4 k a b := by
  simp only [S4, mem_filter, mem_univ, true_and] at hp ⊢
  obtain ⟨⟨hc, hu⟩, h1⟩ := hp
  have hqa : flip4 a b p a = p a := Function.update_of_ne hab _ _
  have hqb : flip4 a b p b = p a ∆ p b := Function.update_self _ _ _
  refine ⟨⟨fun v => ?_, ?_⟩, ?_⟩
  · by_cases hv : v = b
    · subst hv
      rw [hqb]
      have := card_symmDiff_add (p a) (p v)
      rw [h1, hc a, hc v] at this
      omega
    · rw [show flip4 a b p v = p v from Function.update_of_ne hv _ _]; exact hc v
  · ext j
    simp only [mem_biUnion, mem_univ, true_and, iff_true]
    have : j ∈ univ.biUnion p := by rw [hu]; exact mem_univ j
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp this
    by_cases hvb : v = b
    · subst hvb
      by_cases hja : j ∈ p a
      · exact ⟨a, by rw [hqa]; exact hja⟩
      · exact ⟨v, by rw [hqb, mem_symmDiff]; exact Or.inr ⟨hv, hja⟩⟩
    · exact ⟨v, by rw [show flip4 a b p v = p v from Function.update_of_ne hvb _ _]; exact hv⟩
  · rw [hqa, hqb]
    have := card_symmDiff_add (p a) (p a ∆ p b)
    rw [symmDiff_symmDiff_cancel_left, hc a, hc b] at this
    have h2 : (p a ∆ p b).card = 2 := by
      have := card_symmDiff_add (p a) (p b)
      rw [h1, hc a, hc b] at this
      omega
    omega

omit [Fintype V] in
lemma flip4_flip4 {k : ℕ} {a b : V} (hab : a ≠ b) (p : V → Finset (Fin k)) :
    flip4 a b (flip4 a b p) = p := by
  unfold flip4
  rw [Function.update_of_ne hab, Function.update_self, Function.update_idem,
    symmDiff_symmDiff_cancel_left, Function.update_eq_self]

lemma sum_S4_tilde (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (k : ℕ) :
    ∑ p ∈ S4 k a b, edgeSign G p = ∑ p ∈ S4 k a b, edgeSign (tilde G a b) p := by
  apply Finset.sum_nbij' (flip4 a b) (flip4 a b)
  · intro p hp; exact flip4_mem hab hp
  · intro p hp; exact flip4_mem hab hp
  · intro p _; exact flip4_flip4 hab p
  · intro p _; exact flip4_flip4 hab p
  · intro p hp
    simp only [S4, mem_filter, mem_univ, true_and] at hp
    have ha : Even (p a).card := by rw [hp.1.1 a]; decide
    rw [edgeSign_tilde, edgeSign_flip4 G hab p ha, mul_assoc]
    have : ∏ y ∈ Nb G a b, sgnE (flip4 a b p) s(a, y) = ∏ y ∈ Nb G a b, sgnE p s(a, y) := by
      apply Finset.prod_congr rfl
      intro y hy
      simp only [Nb, mem_filter, mem_univ, true_and] at hy
      rw [sgnE_mk, sgnE_mk, show flip4 a b p a = p a from Function.update_of_ne hab _ _,
        show flip4 a b p y = p y from Function.update_of_ne hy.2.1 _ _]
    rw [this, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun e _ => sgnE_sq p _),
      prod_const_one, mul_one]

theorem T_fourT (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (k : ℕ) :
    T k G - T k (toggle G a b) = T k (tilde G a b) - T k (toggle (tilde G a b) a b) := by
  rw [T_sub_toggle G hab, T_sub_toggle _ hab, sum_S4_tilde G hab]

theorem ξ_fourT (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    ξ G - ξ (toggle G a b) = ξ (tilde G a b) - ξ (toggle (tilde G a b) a b) := by
  unfold ξ
  rw [div_sub_div_same, div_sub_div_same, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, ← mul_sub]
  congr 1
  have := T_fourT G hab k
  exact_mod_cast this

theorem T_iso {W : Type} [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (k : ℕ) : T k G = T k H := by
  unfold T
  apply Fintype.sum_equiv (Equiv.arrowCongr e.toEquiv (Equiv.refl (Finset (Fin k))))
  intro p
  have h1 : (∀ w, (Equiv.arrowCongr e.toEquiv (Equiv.refl _) p w).card = 2) ↔
      ∀ v, (p v).card = 2 := by
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
    constructor
    · intro h v
      have := h (e v)
      rwa [show e.toEquiv.symm (e v) = v from e.toEquiv.symm_apply_apply v] at this
    · intro h w; exact h _
  have h2 : univ.biUnion (Equiv.arrowCongr e.toEquiv (Equiv.refl _) p) = univ.biUnion p := by
    ext j
    simp only [mem_biUnion, mem_univ, true_and, Equiv.arrowCongr_apply, Equiv.refl_apply,
      Function.comp_apply]
    constructor
    · rintro ⟨w, h⟩; exact ⟨_, h⟩
    · rintro ⟨v, h⟩
      exact ⟨e v, by rwa [show e.toEquiv.symm (e v) = v from e.toEquiv.symm_apply_apply v]⟩
  have h3 : edgeSign H (Equiv.arrowCongr e.toEquiv (Equiv.refl _) p) = edgeSign G p := by
    rw [edgeSign_eq, edgeSign_eq]
    apply Finset.prod_nbij' (Sym2.map e.symm) (Sym2.map e)
    · intro x hx
      induction x using Sym2.ind with
      | _ x y =>
        simp only [Ed, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet, Sym2.map_mk,
          Set.mem_setOf_eq] at hx ⊢
        exact (e.symm.map_adj_iff).mpr hx
    · intro x hx
      induction x using Sym2.ind with
      | _ x y =>
        simp only [Ed, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet, Sym2.map_mk,
          Set.mem_setOf_eq] at hx ⊢
        exact (e.map_adj_iff).mpr hx
    · intro x _
      induction x using Sym2.ind with
      | _ x y => simp
    · intro x _
      induction x using Sym2.ind with
      | _ x y => simp
    · intro x _
      induction x using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk, sgnE_mk, Equiv.arrowCongr_apply, Equiv.refl_apply,
          Function.comp_apply]
        rfl
  simp only [h1, h2, h3]

theorem ξ_iso {W : Type} [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    ξ G = ξ H := by
  unfold ξ
  rw [Fintype.card_congr e.toEquiv]
  simp_rw [T_iso G H e]

end FourT

/-- `ξ` is a `4`-invariant. -/
theorem ξ_isFourInvariant : IsFourInvariant (fun G => ξ G) :=
  ⟨fun G H ⟨e⟩ => ξ_iso G H e, fun G _ _ hab => ξ_fourT G hab⟩

end SL2W
