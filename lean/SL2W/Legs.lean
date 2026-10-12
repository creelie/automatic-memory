import SL2W.Colour
import SL2W.BosonLabels

/-!
# Lifting the leg words to the oscillator

The bosonic value of a leg word is a sum over the letters `z, ∂` placed on the two legs at
every endpoint, weighted by the pairings of the legs of every chord. Summed over the flags it
is `(-32)ⁿ ξ` of the intersection graph.
-/

open Finset

namespace SL2W

lemma sum_fin_succ_fun {β M : Type*} [Fintype β] [AddCommMonoid M] (m : ℕ)
    (G : (Fin (m + 1) → β) → M) :
    ∑ h, G h = ∑ b : β, ∑ h' : Fin m → β, G (Fin.cons b h') := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => β).symm _ _
    (fun h => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma liftSum_ofFn_pairs {α : Type*} : ∀ (m : ℕ) (x y : Fin m → α) (F : List (α × Fin 2) → ℚ),
    liftSum (List.ofFn fun p => [x p, y p]).flatten F =
      ∑ h : Fin m → Fin 2 × Fin 2,
        F (List.ofFn fun p => [(x p, (h p).1), (y p, (h p).2)]).flatten
  | 0, x, y, F => by simp
  | m + 1, x, y, F => by
    rw [List.ofFn_succ, List.flatten_cons, sum_fin_succ_fun, Fintype.sum_prod_type]
    simp only [List.cons_append, List.nil_append, liftSum_cons]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [liftSum_ofFn_pairs m]
    apply Finset.sum_congr rfl; intro h' _
    simp [List.ofFn_succ]

lemma flatMap_filter_of_nil {γ δ : Type*} (l : List γ) (f : γ → List δ) (P : γ → Bool)
    (h : ∀ x ∈ l, P x = false → f x = []) : l.flatMap f = (l.filter P).flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    by_cases hx : P x = true
    · simp [List.filter_cons, hx, ih']
    · have := h x (by simp) (by simpa using hx)
      simp [List.filter_cons, hx, ih', this]

lemma flatten_ofFn_two {γ : Type*} {m : ℕ} (f : Fin m → List γ) (i j : Fin m) (hij : i < j)
    (hf : ∀ p, p ≠ i → p ≠ j → f p = []) : (List.ofFn f).flatten = f i ++ f j := by
  have e1 : (List.ofFn f).flatten = (List.ofFn id).flatMap f := by
    rw [List.flatMap, List.map_ofFn]; rfl
  rw [e1, flatMap_filter_of_nil _ f (fun p => decide (p = i ∨ p = j))]
  · rw [ofFn_filter_eq id _ [i, j]]
    · simp
    · exact List.pairwise_pair.mpr hij
    · intro p; simp
  · intro p _ hp
    simp only [decide_eq_false_iff_not, not_or] at hp
    exact hf p hp.1 hp.2

lemma piece_eq {α : Type*} [LinearOrder α] (u v w : α) (a b : Fin 2) :
    (([(u, a), (v, b)] : List (α × Fin 2)).filter (isL w)).map Prod.snd =
      (if u = w then [a] else []) ++ (if v = w then [b] else []) := by
  simp only [List.filter_cons, List.filter_nil, isL]
  by_cases hu : u = w <;> by_cases hv : v = w <;> simp [hu, hv]

/-- The pairing of the four legs of a chord: the first and second endpoint carry the letter
pairs `x` and `y`, and the legs are matched crosswise when the chord is flagged. -/
def pairK (b : Fin 2) (x y : Fin 2 × Fin 2) : ℚ :=
  if b = 1 then pairW [x.1, y.2] * pairW [x.2, y.1] else pairW [x.1, y.1] * pairW [x.2, y.2]

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

/-- The label of the first leg at an endpoint. -/
def lx (β' : D.Chord → Fin 2) (p : Fin (2 * n)) : D.Lab :=
  if D.flag β' p then D.lab (D.chordOf p) 1 else D.lab (D.chordOf p) 0

/-- The label of the second leg at an endpoint. -/
def ly (β' : D.Chord → Fin 2) (p : Fin (2 * n)) : D.Lab :=
  if D.flag β' p then D.lab (D.chordOf p) 0 else D.lab (D.chordOf p) 1

lemma legL_eq (β' : D.Chord → Fin 2) :
    D.legL β' = (List.ofFn fun p => [D.lx β' p, D.ly β' p]).flatten := by
  unfold legL legW
  rw [List.flatMap, List.map_ofFn]
  congr 2
  funext p
  simp only [Function.comp_apply, blk, lx, ly]
  split <;> rfl

/-- The labelled lift of a leg word. -/
def legZ (β' : D.Chord → Fin 2) (h : Fin (2 * n) → Fin 2 × Fin 2) : List (D.Lab × Fin 2) :=
  (List.ofFn fun p => [(D.lx β' p, (h p).1), (D.ly β' p, (h p).2)]).flatten

end ChordDiagram

/-- The letters of a lift. -/
def flat {m : ℕ} (h : Fin m → Fin 2 × Fin 2) : List (Fin 2) :=
  (List.ofFn fun p => [(h p).1, (h p).2]).flatten

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma legZ_snd (β' : D.Chord → Fin 2) (h : Fin (2 * n) → Fin 2 × Fin 2) :
    (D.legZ β' h).map Prod.snd = flat h := by
  simp [legZ, flat, List.map_flatten, List.map_ofFn, Function.comp_def]

lemma flag_first (β' : D.Chord → Fin 2) (c : D.Chord) : D.flag β' c.1 = false := by
  simp [flag, c.2]

lemma flag_second (β' : D.Chord → Fin 2) (c : D.Chord) :
    D.flag β' (D.σ c.1) = decide (β' c = 1) := by
  simp [flag, D.invol, not_lt.mpr c.2.le, D.chordOf_σ]

lemma legZ_filter (β' : D.Chord → Fin 2) (h : Fin (2 * n) → Fin 2 × Fin 2) (w : D.Lab)
    (c : D.Chord) (hw : ∀ p, (D.lx β' p = w ∨ D.ly β' p = w) → D.chordOf p = c) :
    ((D.legZ β' h).filter (isL w)).map Prod.snd =
      ((if D.lx β' c.1 = w then [(h c.1).1] else []) ++
        (if D.ly β' c.1 = w then [(h c.1).2] else [])) ++
      ((if D.lx β' (D.σ c.1) = w then [(h (D.σ c.1)).1] else []) ++
        (if D.ly β' (D.σ c.1) = w then [(h (D.σ c.1)).2] else [])) := by
  unfold legZ
  rw [List.filter_flatten, List.map_flatten, List.map_ofFn, List.map_ofFn]
  rw [flatten_ofFn_two _ c.1 (D.σ c.1) c.2]
  · simp only [Function.comp_apply, piece_eq]
    split_ifs <;> rfl
  · intro p h1 h2
    have hc : D.chordOf p ≠ c := by
      rw [Ne, D.chordOf_eq_iff]; tauto
    simp only [Function.comp_apply, piece_eq]
    have hx : D.lx β' p ≠ w := fun e => hc (hw p (Or.inl e))
    have hy : D.ly β' p ≠ w := fun e => hc (hw p (Or.inr e))
    simp [hx, hy]

lemma lab_chord {β' : D.Chord → Fin 2} {c : D.Chord} {j : Fin 2} :
    ∀ p, (D.lx β' p = D.lab c j ∨ D.ly β' p = D.lab c j) → D.chordOf p = c := by
  intro p hp
  unfold lx ly at hp
  split at hp <;> rcases hp with e | e <;> exact ((D.lab_inj).mp e).1

lemma wt_legZ (β' : D.Chord → Fin 2) (h : Fin (2 * n) → Fin 2 × Fin 2) :
    wt (D.legZ β' h) = ∏ c, pairK (β' c) (h c.1) (h (D.σ c.1)) := by
  unfold wt
  rw [← Fintype.prod_equiv toLex (fun cj : D.Chord × Fin 2 =>
    pairW (((D.legZ β' h).filter (isL (toLex cj))).map Prod.snd)) _ (fun _ => rfl),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fin.prod_univ_two]
  have e0 := D.legZ_filter β' h (D.lab c 0) c D.lab_chord
  have e1 := D.legZ_filter β' h (D.lab c 1) c D.lab_chord
  simp only [lab] at e0 e1
  rw [e0, e1]
  have f1 := D.flag_first β' c
  have f2 := D.flag_second β' c
  simp only [lx, ly, f1, f2, D.chordOf_self, D.chordOf_σ]
  rcases Fin.exists_fin_two.mp ⟨β' c, rfl⟩ with hb | hb <;>
    simp [hb, pairK, lab]

theorem Zb_legL (β' : D.Chord → Fin 2) :
    Zb (D.legL β') = ∑ h : Fin (2 * n) → Fin 2 × Fin 2,
      (∏ c, pairK (β' c) (h c.1) (h (D.σ c.1))) * τb (flat h) := by
  unfold Zb
  rw [D.legL_eq, liftSum_ofFn_pairs]
  apply Finset.sum_congr rfl
  intro h _
  rw [show (List.ofFn fun p => [(D.lx β' p, (h p).1), (D.ly β' p, (h p).2)]).flatten =
    D.legZ β' h from rfl, D.wt_legZ, D.legZ_snd]

lemma τF_legL_self (β' : D.Chord → Fin 2) : τF (D.legL β') = (-1) ^ n * D.sgn β' := by
  classical
  have h := D.τF_legL β' id
  rw [List.map_id] at h
  simp only [id_eq] at h
  rw [h, D.τF_gauss _ (fun c => by simp [lab])]
  have hE : ∏ e ∈ D.interGraph.edgeFinset, (-1 : ℤ) ^ (Sym2.lift
      ⟨mpair (fun c => (D.lab c 0, D.lab c 1)), D.mpair_comm _⟩ e) = 1 := by
    apply Finset.prod_eq_one
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hab : a ≠ b := D.interGraph.ne_of_adj he
      simp [Sym2.lift_mk, mpair, D.lab_inj, hab]
  rw [hE, sgn, mul_one, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro c _
  simp [D.lab_inj]

theorem sum_Zb_legL :
    ∑ β' : D.Chord → Fin 2, Zb (D.legL β') = (Sp D.interGraph).eval (-2) := by
  have hZ : ∀ β' : D.Chord → Fin 2, Zb (D.legL β') =
      (1 / 2 : ℚ) ^ (2 * n) * (-1) ^ n * ((D.sgn β' : ℚ) * (Pol (D.legL β')).eval (-2)) := by
    intro β'
    rw [Zb_eq (2 * n) (D.legL β') (D.legL_length β') (D.legL_DO β'), D.τF_legL_self]
    push_cast
    ring
  simp_rw [hZ]
  rw [← Finset.mul_sum]
  have hP := congrArg (Polynomial.eval (-2 : ℚ)) D.sum_sgn_Pol
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C] at hP
  rw [hP, pow_mul, ← mul_assoc, ← mul_pow, ← mul_pow]
  norm_num

/-- The bosonic form of `ξ`. -/
theorem boson_graph :
    ∑ β' : D.Chord → Fin 2, ∑ h : Fin (2 * n) → Fin 2 × Fin 2,
      (∏ c, pairK (β' c) (h c.1) (h (D.σ c.1))) * τb (flat h) =
        (-32 : ℚ) ^ n * ξ D.interGraph := by
  simp_rw [← D.Zb_legL]
  rw [D.sum_Zb_legL, ξ_eq_Sp, D.card_chord]
  have : ((-32 : ℚ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end ChordDiagram

end SL2W
