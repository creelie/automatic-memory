import SL2W.Gauss
import SL2W.Graph

/-!
# The leg words of a chord diagram and their colour sums

Every endpoint of a chord carries two legs labelled by the chord and an index in `{0, 1}`;
at the second endpoint of a chord the two legs are exchanged when the chord is flagged.
The signed sum over the flags of the loop polynomials of these words is `(-4)ⁿ Sp`.
-/

open Finset

namespace SL2W

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma card_chord : Fintype.card D.Chord = n := by
  rw [Fintype.card_subtype]
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * n))))
    (fun i => i < D.σ i)
  have h2 : (univ.filter fun i => ¬ i < D.σ i).card = (univ.filter fun i => i < D.σ i).card := by
    apply Finset.card_nbij' D.σ D.σ
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [D.invol]; exact lt_of_le_of_ne (not_lt.mp hi) (D.nofix i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [D.invol]; exact not_lt.mpr hi.le
    · intro i _; exact D.invol i
    · intro i _; exact D.invol i
  rw [card_univ, Fintype.card_fin, h2] at h1
  omega

/-- The labels of the legs. -/
abbrev Lab := Lex (D.Chord × Fin 2)

/-- The label of the leg `j` of the chord `c`. -/
def lab (c : D.Chord) (j : Fin 2) : D.Lab := toLex (c, j)

lemma lab_inj {c c' : D.Chord} {j j' : Fin 2} : D.lab c j = D.lab c' j' ↔ c = c' ∧ j = j' := by
  simp [lab]

lemma card_lab : Fintype.card D.Lab = 2 * n := by
  simp [Fintype.card_lex, D.card_chord, mul_comm]

/-- The second endpoint `p` of a flagged chord. -/
def flag (β' : D.Chord → Fin 2) (p : Fin (2 * n)) : Bool :=
  decide (¬ p < D.σ p ∧ β' (D.chordOf p) = 1)

/-- The blocks of legs along the circle. -/
def legW (β' : D.Chord → Fin 2) : List (D.Lab × D.Lab × Bool) :=
  List.ofFn fun p => (D.lab (D.chordOf p) 0, D.lab (D.chordOf p) 1, D.flag β' p)

/-- The word of leg labels. -/
def legL (β' : D.Chord → Fin 2) : List D.Lab := (D.legW β').flatMap blk

lemma flatMap_blk_map {β γ : Type*} [LinearOrder β] [LinearOrder γ] (f : β → γ)
    (ws : List (β × β × Bool)) :
    (ws.flatMap blk).map f = (ws.map fun w => (f w.1, f w.2.1, w.2.2)).flatMap blk := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.map_append, ih, List.map_cons]
    congr 1
    unfold blk
    split <;> simp_all

lemma legL_map {γ : Type*} [LinearOrder γ] (β' : D.Chord → Fin 2) (col : D.Lab → γ) :
    (D.legL β').map col = (List.ofFn fun p => (col (D.lab (D.chordOf p) 0),
      col (D.lab (D.chordOf p) 1), D.flag β' p)).flatMap blk := by
  unfold legL legW
  rw [flatMap_blk_map, List.map_ofFn]
  rfl

lemma prod_second {M : Type*} [CommMonoid M] (G : D.Chord → M) :
    ∏ p : Fin (2 * n), (if ¬ p < D.σ p then G (D.chordOf p) else 1) = ∏ c, G c := by
  rw [← Finset.prod_filter]
  apply Finset.prod_nbij' (fun p => D.chordOf p) (fun c => D.σ c.1)
  · intro p _; exact mem_univ _
  · intro c _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [D.invol]; exact not_lt.mpr c.2.le
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [D.chordOf_val, if_neg hp, D.invol]
  · intro c _; exact D.chordOf_σ c
  · intro p _; rfl

/-- The sign of the leg word under a colouring. -/
lemma τF_legL {γ : Type*} [LinearOrder γ] (β' : D.Chord → Fin 2) (col : D.Lab → γ) :
    τF ((D.legL β').map col) =
      (∏ c, if β' c = 1 ∧ col (D.lab c 0) ≠ col (D.lab c 1) then (-1 : ℤ) else 1) *
        τF (blocks (fun c => (col (D.lab c 0), col (D.lab c 1))) D.gauss) := by
  rw [D.legL_map]
  have h := τF_flip (List.ofFn fun p => (col (D.lab (D.chordOf p) 0),
      col (D.lab (D.chordOf p) 1), D.flag β' p)) []
  simp only [List.nil_append] at h
  rw [h]
  congr 1
  · rw [List.map_ofFn, List.prod_ofFn, ← D.prod_second]
    apply Finset.prod_congr rfl
    intro p _
    simp only [Function.comp_apply, flipSign, flag, decide_eq_true_eq]
    by_cases hp : p < D.σ p
    · simp [hp]
    · simp [hp]
  · unfold blocks gauss
    simp [List.flatMap, List.map_ofFn, blk0, Function.comp_def]

/-- The sign `(-1)^{|β'|}` of a set of flags. -/
def sgn (β' : D.Chord → Fin 2) : ℤ := ∏ c, if β' c = 1 then -1 else 1

lemma sum_sgn_τF {γ : Type*} [LinearOrder γ] (col : D.Lab → γ) :
    ∑ β' : D.Chord → Fin 2, D.sgn β' * τF ((D.legL β').map col) =
      (∏ c, if col (D.lab c 0) ≠ col (D.lab c 1) then (2 : ℤ) else 0) *
        τF (blocks (fun c => (col (D.lab c 0), col (D.lab c 1))) D.gauss) := by
  simp only [D.τF_legL, sgn, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [← Finset.sum_mul]
  congr 1
  have e := Fintype.prod_sum (fun (c : D.Chord) (b : Fin 2) =>
    (if b = 1 then (-1 : ℤ) else 1) * (if b = 1 ∧ col (D.lab c 0) ≠ col (D.lab c 1) then -1 else 1))
  rw [← e]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fin.sum_univ_two]
  by_cases h : col (D.lab c 0) = col (D.lab c 1) <;> simp [h]

/-- Colourings of the legs as pairs of colours on the chords. -/
def pairsEquiv (γ : Type*) : (D.Lab → γ) ≃ (D.Chord → γ × γ) where
  toFun col c := (col (D.lab c 0), col (D.lab c 1))
  invFun κ l := if (ofLex l).2 = 0 then (κ (ofLex l).1).1 else (κ (ofLex l).1).2
  left_inv col := by
    funext l
    obtain ⟨c, j⟩ := l
    fin_cases j <;> rfl
  right_inv κ := by
    funext c
    simp [lab]

lemma blk_length {β : Type*} [LinearOrder β] (w : β × β × Bool) : (blk w).length = 2 := by
  unfold blk; split <;> rfl

lemma count_blk {β : Type*} [LinearOrder β] (a : β) (w : β × β × Bool) :
    (blk w).count a = (blk0 w).count a := by
  unfold blk blk0
  split
  · simp only [List.count_cons, List.count_nil, beq_iff_eq]; omega
  · rfl

lemma count_flatMap_blk {β : Type*} [LinearOrder β] (a : β) (ws : List (β × β × Bool)) :
    (ws.flatMap blk).count a = (ws.map fun w => (blk0 w).count a).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, List.count_append, count_blk, ih]

lemma legL_length (β' : D.Chord → Fin 2) : (D.legL β').length = 2 * (2 * n) := by
  unfold legL legW
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, blk_length, List.sum_ofFn, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

lemma legL_DO (β' : D.Chord → Fin 2) : DO (D.legL β') := by
  intro a _
  rw [show a = D.lab (ofLex a).1 (ofLex a).2 from rfl]
  generalize (ofLex a).1 = c
  generalize (ofLex a).2 = j
  unfold legL legW
  rw [count_flatMap_blk, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, blk0, List.count_cons, List.count_nil, beq_iff_eq, D.lab_inj]
  have e : ∀ p : Fin (2 * n), ((if D.chordOf p = c ∧ (1 : Fin 2) = j then 1 else 0) +
      (if D.chordOf p = c ∧ (0 : Fin 2) = j then 1 else 0) : ℕ) =
      if D.chordOf p = c then 1 else 0 := by
    intro p
    by_cases hp : D.chordOf p = c
    · fin_cases j <;> simp [hp]
    · simp [hp]
  simp only [zero_add, e]
  rw [Finset.sum_boole]
  have : (univ.filter fun p => D.chordOf p = c) = {c.1, D.σ c.1} := by
    ext p
    simp [D.chordOf_eq_iff]
  rw [this, Finset.card_pair (ne_of_lt c.2)]
  rfl

lemma prod_mpair_eq_edgeSign [Fintype D.interGraph.edgeSet] {N : ℕ}
    (κ : D.Chord → Fin N × Fin N) (hκ : ∀ c, (κ c).1 ≠ (κ c).2) :
    ∏ e ∈ D.interGraph.edgeFinset, (-1 : ℤ) ^ (Sym2.lift ⟨mpair κ, D.mpair_comm κ⟩ e) =
      edgeSign D.interGraph (fun c => {(κ c).1, (κ c).2}) := by
  unfold edgeSign
  apply Finset.prod_congr
  · ext e; simp [SimpleGraph.mem_edgeFinset]
  · intro e _
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.lift_mk]
      rw [card_pair_inter (hκ a) (hκ b)]
      rfl

theorem colour_sum_int (N : ℕ) :
    ∑ κ : D.Chord → Fin N × Fin N,
        (∏ c, if (κ c).1 ≠ (κ c).2 then (2 : ℤ) else 0) * τF (blocks κ D.gauss) =
      (-4 : ℤ) ^ n * ∑ k ∈ range (N + 1), (N.choose k : ℤ) * T k D.interGraph := by
  classical
  have h1 : ∀ κ : D.Chord → Fin N × Fin N,
      (∏ c, if (κ c).1 ≠ (κ c).2 then (2 : ℤ) else 0) * τF (blocks κ D.gauss) =
        2 ^ n * (-1) ^ n * (if ∀ c, (κ c).1 ≠ (κ c).2 then
          edgeSign D.interGraph (fun c => {(κ c).1, (κ c).2}) else 0) := by
    intro κ
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff, Finset.prod_const, Finset.card_univ, D.card_chord]
    by_cases hκ : ∀ c, (κ c).1 ≠ (κ c).2
    · rw [if_pos hκ, if_pos hκ, D.τF_gauss κ hκ, D.prod_mpair_eq_edgeSign κ hκ]
      ring
    · rw [if_neg hκ, if_neg hκ]; ring
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_pairs_fiber N (edgeSign D.interGraph), sum_card_two, D.card_chord,
    show ((-4 : ℤ)) ^ n = 2 ^ n * (-1) ^ n * 2 ^ n by rw [← mul_pow, ← mul_pow]; norm_num]
  ring

theorem colour_sum (N : ℕ) :
    ∑ β' : D.Chord → Fin 2, (D.sgn β' : ℚ) * Gf N (D.legL β') =
      (-4 : ℚ) ^ n * ∑ k ∈ range (N + 1), (N.choose k : ℚ) * T k D.interGraph := by
  unfold Gf
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ col : D.Lab → Fin N, ∑ β' : D.Chord → Fin 2,
      (D.sgn β' : ℚ) * (τF ((D.legL β').map col) : ℚ) =
      (((∏ c, if col (D.lab c 0) ≠ col (D.lab c 1) then (2 : ℤ) else 0) *
        τF (blocks (fun c => (col (D.lab c 0), col (D.lab c 1))) D.gauss) : ℤ) : ℚ) := by
    intro col
    rw [← D.sum_sgn_τF col]
    push_cast
    rfl
  simp_rw [h1]
  rw [Finset.sum_equiv (D.pairsEquiv (Fin N)) (t := univ)
    (g := fun κ => (((∏ c, if (κ c).1 ≠ (κ c).2 then (2 : ℤ) else 0) *
      τF (blocks κ D.gauss) : ℤ) : ℚ)) ?_ ?_]
  rotate_left
  · simp
  · intro col _; rfl
  rw [← Int.cast_sum, D.colour_sum_int]
  push_cast
  rw [Finset.mul_sum]

/-- The signed sum of the loop polynomials of the leg words. -/
theorem sum_sgn_Pol :
    ∑ β' : D.Chord → Fin 2, Polynomial.C (D.sgn β' : ℚ) * Pol (D.legL β') =
      Polynomial.C ((-4 : ℚ) ^ n) * Sp D.interGraph := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun N : ℕ => ((N + 1 : ℕ) : ℚ))
  · intro a b h
    simp only [Nat.cast_inj, add_left_inj] at h
    exact h
  · intro N
    generalize hM : N + 1 = M
    have hM0 : M ≠ 0 := by omega
    simp only [Set.mem_setOf_eq, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [Sp_eval_nat]
    have hG : ∀ β', (Pol (D.legL β')).eval (M : ℚ) = Gf M (D.legL β') := by
      intro β'
      have h := Gf_Pol M (2 * n) (D.legL β') (D.legL_length β') (D.legL_DO β')
      rw [D.card_lab] at h
      have hne : (M : ℚ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0)
      exact (mul_left_cancel₀ hne h).symm
    simp_rw [hG]
    rw [D.colour_sum]

end ChordDiagram

end SL2W
