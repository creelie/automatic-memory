import SL2W.Defs
import SL2W.Blocks

/-!
# The Gauss word of a chord diagram

Reading the chords along the circle gives a word in which every chord occurs twice. Two chords
alternate in this word exactly when they are adjacent in the intersection graph.
-/

open Finset

namespace SL2W

/-- Filtering a tuple read as a list. -/
lemma ofFn_filter_eq {γ : Type*} {m : ℕ} (f : Fin m → γ) (P : γ → Bool) (l : List (Fin m))
    (hs : l.Pairwise (· < ·)) (hm : ∀ p, p ∈ l ↔ P (f p) = true) :
    (List.ofFn f).filter P = l.map f := by
  rw [List.ofFn_eq_map, List.filter_map]
  congr 1
  apply List.Perm.eq_of_pairwise (le := (· < ·))
  · intro a b _ _ h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  · exact (List.pairwise_lt_finRange m).filter _
  · exact hs
  · rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange m).filter _) (hs.imp ne_of_lt)]
    intro p
    simp [hm]

lemma pw4 {m : ℕ} {a b c d : Fin m} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    [a, b, c, d].Pairwise (· < ·) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
  refine ⟨?_, ?_, ?_, by simp⟩
  · rintro x (rfl | rfl | rfl | h) <;> first | order | exact h.elim
  · rintro x (rfl | rfl | h) <;> first | order | exact h.elim
  · rintro x (rfl | h) <;> first | order | exact h.elim

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

lemma σ_lt_of_not_lt {p : Fin (2 * n)} (h : ¬ p < D.σ p) : D.σ p < D.σ (D.σ p) := by
  rw [D.invol]; exact lt_of_le_of_ne (not_lt.mp h) (D.nofix p)

/-- The chord through a point. -/
def chordOf (p : Fin (2 * n)) : D.Chord :=
  if h : p < D.σ p then ⟨p, h⟩ else ⟨D.σ p, D.σ_lt_of_not_lt h⟩

lemma chordOf_val (p : Fin (2 * n)) :
    (D.chordOf p).1 = if p < D.σ p then p else D.σ p := by
  unfold chordOf
  by_cases h : p < D.σ p
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

lemma chordOf_eq_iff (p : Fin (2 * n)) (c : D.Chord) :
    D.chordOf p = c ↔ p = c.1 ∨ p = D.σ c.1 := by
  rw [Subtype.ext_iff, chordOf_val]
  obtain ⟨i, hi⟩ := c
  simp only
  by_cases h : p < D.σ p
  · rw [if_pos h]
    constructor
    · exact Or.inl
    · rintro (e | e)
      · exact e
      · exfalso
        have h1 : D.σ p = i := by rw [e, D.invol]
        rw [h1] at h
        rw [← e] at hi
        exact absurd (h.trans hi) (lt_irrefl _)
  · rw [if_neg h]
    constructor
    · intro e; right; rw [← e, D.invol]
    · rintro (e | e)
      · subst e; exact absurd hi h
      · rw [e, D.invol]

lemma chordOf_self (c : D.Chord) : D.chordOf c.1 = c := (D.chordOf_eq_iff _ _).mpr (Or.inl rfl)

lemma chordOf_σ (c : D.Chord) : D.chordOf (D.σ c.1) = c :=
  (D.chordOf_eq_iff _ _).mpr (Or.inr rfl)

/-- The Gauss word of the chord diagram. -/
def gauss : List D.Chord := List.ofFn D.chordOf

lemma gauss_length : D.gauss.length = 2 * n := by simp [gauss]

lemma gauss_DO : DO D.gauss := by
  intro c _
  unfold List.count
  rw [List.countP_eq_length_filter]
  unfold gauss
  rw [ofFn_filter_eq D.chordOf _ [c.1, D.σ c.1] (by simpa using c.2)]
  · rfl
  · intro p
    simp [D.chordOf_eq_iff]

lemma crs_gauss_of (u v : D.Chord) (l : List (Fin (2 * n))) (hs : l.Pairwise (· < ·))
    (hm : ∀ p, p ∈ l ↔ (p = u.1 ∨ p = D.σ u.1 ∨ p = v.1 ∨ p = D.σ v.1)) :
    crs D.gauss u v ↔ l.map D.chordOf = [u, v, u, v] := by
  unfold crs gauss
  rw [ofFn_filter_eq D.chordOf _ l hs]
  intro p
  rw [hm]
  simp only [D.chordOf_eq_iff, decide_eq_true_eq]
  tauto

lemma crs_gauss_iff (u v : D.Chord) :
    crs D.gauss u v ↔ u.1 < v.1 ∧ v.1 < D.σ u.1 ∧ D.σ u.1 < D.σ v.1 := by
  obtain ⟨i, hi⟩ := u
  obtain ⟨j, hj⟩ := v
  simp only
  have cu : D.chordOf i = ⟨i, hi⟩ := D.chordOf_self ⟨i, hi⟩
  have cu' : D.chordOf (D.σ i) = ⟨i, hi⟩ := D.chordOf_σ ⟨i, hi⟩
  have cv : D.chordOf j = ⟨j, hj⟩ := D.chordOf_self ⟨j, hj⟩
  have cv' : D.chordOf (D.σ j) = ⟨j, hj⟩ := D.chordOf_σ ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij
    rw [D.crs_gauss_of _ _ [i, D.σ i] (by simpa using hi) (by intro p; simp <;> tauto)]
    simp [cu, cu']
  have huv : (⟨i, hi⟩ : D.Chord) ≠ ⟨j, hj⟩ := fun e => hij (congrArg Subtype.val e)
  have hij' : i ≠ D.σ j := by
    intro e
    have h1 : D.σ i = j := by rw [e, D.invol]
    have := hi
    rw [h1, e] at this
    exact absurd (hj.trans this) (lt_irrefl _)
  have hi'j : D.σ i ≠ j := by
    intro e
    have h1 : D.σ j = i := by rw [← e, D.invol]
    have := hj
    rw [h1, ← e] at this
    exact absurd (hi.trans this) (lt_irrefl _)
  have hi'j' : D.σ i ≠ D.σ j := by
    intro e
    apply hij
    have := congrArg D.σ e
    rwa [D.invol, D.invol] at this
  have key : ∀ l : List (Fin (2 * n)), l.Pairwise (· < ·) →
      (∀ p, p ∈ l ↔ (p = i ∨ p = D.σ i ∨ p = j ∨ p = D.σ j)) →
      (crs D.gauss ⟨i, hi⟩ ⟨j, hj⟩ ↔ l.map D.chordOf = [⟨i, hi⟩, ⟨j, hj⟩, ⟨i, hi⟩, ⟨j, hj⟩]) :=
    fun l hs hm => D.crs_gauss_of _ _ l hs hm
  rcases lt_or_gt_of_ne hij with h1 | h1
  · rcases lt_or_gt_of_ne hi'j with h2 | h2
    · rw [key [i, D.σ i, j, D.σ j] (pw4 hi h2 hj) (by intro p; simp <;> tauto)]
      simp only [List.map_cons, List.map_nil, cu, cu', cv, cv']
      constructor
      · intro h; simp only [List.cons.injEq] at h; exact absurd h.2.1 huv
      · rintro ⟨-, h, -⟩; exact absurd h (not_lt.mpr h2.le)
    · rcases lt_or_gt_of_ne hi'j' with h3 | h3
      · rw [key [i, j, D.σ i, D.σ j] (pw4 h1 h2 h3) (by intro p; simp <;> tauto)]
        simp only [List.map_cons, List.map_nil, cu, cu', cv, cv']
        exact ⟨fun _ => ⟨h1, h2, h3⟩, fun _ => trivial⟩
      · rw [key [i, j, D.σ j, D.σ i] (pw4 h1 hj h3) (by intro p; simp <;> tauto)]
        simp only [List.map_cons, List.map_nil, cu, cu', cv, cv']
        constructor
        · intro h
          simp only [List.cons.injEq] at h
          exact absurd h.2.2.1 huv.symm
        · rintro ⟨-, -, h⟩; exact absurd h (not_lt.mpr h3.le)
  · have hfalse : ¬ (i < j ∧ j < D.σ i ∧ D.σ i < D.σ j) :=
      fun h => absurd h.1 (not_lt.mpr h1.le)
    have hhead : ∀ t : List (Fin (2 * n)),
        (j :: t).map D.chordOf ≠ [⟨i, hi⟩, ⟨j, hj⟩, ⟨i, hi⟩, ⟨j, hj⟩] := by
      intro t h
      simp only [List.map_cons, cv, List.cons.injEq] at h
      exact huv h.1.symm
    rcases lt_or_gt_of_ne (Ne.symm hij') with h2 | h2
    · rw [key [j, D.σ j, i, D.σ i] (pw4 hj h2 hi) (by intro p; simp <;> tauto)]
      exact ⟨fun h => absurd h (hhead _), fun h => absurd h hfalse⟩
    · rcases lt_or_gt_of_ne hi'j' with h3 | h3
      · rw [key [j, i, D.σ i, D.σ j] (pw4 h1 hi h3) (by intro p; simp <;> tauto)]
        exact ⟨fun h => absurd h (hhead _), fun h => absurd h hfalse⟩
      · rw [key [j, i, D.σ j, D.σ i] (pw4 h1 h2 h3) (by intro p; simp <;> tauto)]
        exact ⟨fun h => absurd h (hhead _), fun h => absurd h hfalse⟩

lemma Xc_gauss [Fintype D.interGraph.edgeSet] (m : D.Chord → D.Chord → ℕ)
    (hm : ∀ u v, m u v = m v u) :
    Xc D.gauss m = ∑ e ∈ D.interGraph.edgeFinset, Sym2.lift ⟨m, hm⟩ e := by
  unfold Xc
  rw [← Finset.sum_product' (f := fun u v => if crs D.gauss u v then m u v else 0),
    ← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    show D.crosses p.1.1 p.2.1
    exact Or.inl ((D.crs_gauss_iff _ _).mp hp)
  · intro p hp q hq e
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      D.crs_gauss_iff] at hp hq
    rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have a1 : p.1.1 < p.2.1 := hp.1
      have a2 : q.1.1 < q.2.1 := hq.1
      rw [h1, h2] at a1
      exact absurd (a1.trans a2) (lt_irrefl _)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases he with h | h
      · exact ⟨(a, b), by simpa [D.crs_gauss_iff] using h, rfl⟩
      · exact ⟨(b, a), by simpa [D.crs_gauss_iff] using h, Sym2.eq_swap⟩
  · intro p _
    rfl

lemma mpair_comm {β : Type*} [LinearOrder β] (κ : D.Chord → β × β) (u v : D.Chord) :
    mpair κ u v = mpair κ v u := by
  unfold mpair
  simp only [eq_comm]
  omega

/-- The sign of the block word along the Gauss word. -/
theorem τF_gauss {β : Type*} [LinearOrder β] [Fintype D.interGraph.edgeSet]
    (κ : D.Chord → β × β) (hκ : ∀ c, (κ c).1 ≠ (κ c).2) :
    τF (blocks κ D.gauss) = (-1) ^ n *
      ∏ e ∈ D.interGraph.edgeFinset, (-1) ^ (Sym2.lift ⟨mpair κ, D.mpair_comm κ⟩ e) := by
  rw [τF_blocks κ hκ n D.gauss D.gauss_length D.gauss_DO, D.Xc_gauss _ (D.mpair_comm κ),
    Finset.prod_pow_eq_pow_sum]

end ChordDiagram

end SL2W
