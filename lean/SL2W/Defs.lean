import Mathlib

/-!
# Definitions: chord diagrams, the `sl(2)` weight system, intersection graphs and `ξ`
-/

open Finset

namespace SL2W

/-- A chord diagram with `n` chords: the `2n` endpoints are the points `0, …, 2n-1`
of the circle cut at a base point, and `σ` sends an endpoint to the other endpoint
of its chord. -/
structure ChordDiagram (n : ℕ) where
  σ : Fin (2 * n) → Fin (2 * n)
  invol : ∀ i, σ (σ i) = i
  nofix : ∀ i, σ i ≠ i

/-- Coefficients of the Casimir tensor `t = ¼ E⊗F + ¼ F⊗E + ⅛ H⊗H` of `sl(2)` for the
Killing form, in the basis `0 = E`, `1 = F`, `2 = H`. -/
def tcoef : Fin 3 → Fin 3 → ℚ
  | 0, 1 => 1 / 4
  | 1, 0 => 1 / 4
  | 2, 2 => 1 / 8
  | _, _ => 0

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

/-- The first endpoints of the chords. -/
def firsts : Finset (Fin (2 * n)) := univ.filter fun i => i < D.σ i

/-- The weight of a labelling `β` of the endpoints by basis letters. -/
def weight (β : Fin (2 * n) → Fin 3) : ℚ :=
  ∏ i ∈ D.firsts, tcoef (β i) (β (D.σ i))

/-- The element of an algebra obtained by placing the Casimir tensor on every chord and
multiplying along the circle. -/
def casimirWord {A : Type*} [Ring A] [Algebra ℚ A] (x : Fin 3 → A) : A :=
  ∑ β : Fin (2 * n) → Fin 3, D.weight β • (List.ofFn fun i => x (β i)).prod

/-- The vertices of the intersection graph: the chords, each named by its first endpoint. -/
abbrev Chord := {i : Fin (2 * n) // i < D.σ i}


/-- Two chords are adjacent in the intersection graph when their endpoints alternate. -/
def crosses (a b : Fin (2 * n)) : Prop :=
  (a < b ∧ b < D.σ a ∧ D.σ a < D.σ b) ∨ (b < a ∧ a < D.σ b ∧ D.σ b < D.σ a)

/-- The intersection graph of a chord diagram. -/
def interGraph : SimpleGraph D.Chord where
  Adj a b := D.crosses a.1 b.1
  symm := ⟨fun a b h => by
    simp only [crosses] at *
    tauto⟩
  loopless := ⟨fun a h => by
    simp only [crosses] at h
    rcases h with h | h <;> exact lt_irrefl _ h.1⟩

end ChordDiagram

/-- The irreducible representation of `sl(2)` of dimension `d`, in the basis
`e₀, …, e_{d-1}` with `E e_s = s(d-s) e_{s-1}`, `F e_s = e_{s+1}`, `H e_s = (d-1-2s) e_s`. -/
def sl2Rep (d : ℕ) : Fin 3 → Matrix (Fin d) (Fin d) ℚ
  | 0 => Matrix.of fun r s => if (s : ℕ) = r + 1 then (s : ℚ) * ((d : ℚ) - s) else 0
  | 1 => Matrix.of fun r s => if (r : ℕ) = s + 1 then 1 else 0
  | 2 => Matrix.diagonal fun s => (d : ℚ) - 1 - 2 * s

/-- The `sl(2)` weight system in the `d`-dimensional representation, normalised by `1/d`. -/
noncomputable def W (d : ℕ) {n : ℕ} (D : ChordDiagram n) : ℚ :=
  Matrix.trace (D.casimirWord (sl2Rep d)) / d

section Graphs

variable {V : Type} [Fintype V]

/-- Toggle the edge `ab`. -/
def toggle (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ Xor (G.Adj x y) ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rcases h with ⟨_, h⟩
    simp only [xor_def] at *
    rw [G.adj_comm]
    tauto⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Replace the neighbourhood of `a` outside `{a, b}` by its symmetric difference with the
neighbourhood of `b`. -/
def tilde (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ Xor (G.Adj x y) ((x = a ∧ y ≠ b ∧ G.Adj b y) ∨ (y = a ∧ x ≠ b ∧ G.Adj b x))
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rcases h with ⟨_, h⟩
    simp only [xor_def] at *
    rw [G.adj_comm]
    tauto⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

open Classical in
/-- The sign of an assignment of subsets to the vertices: `(-1)` to the sum over the edges
`xy` of `|p x ∩ p y|`. -/
noncomputable def edgeSign {k : ℕ} (G : SimpleGraph V) (p : V → Finset (Fin k)) : ℤ :=
  ∏ e ∈ G.edgeFinset,
    (-1) ^ (Sym2.lift ⟨fun a b => (p a ∩ p b).card, fun a b => by simp only [inter_comm]⟩ e)

open Classical in
/-- `T k G`: the signed number of ways to assign to every vertex a `2`-element subset of
`{0, …, k-1}` so that every element is used. -/
noncomputable def T (k : ℕ) (G : SimpleGraph V) : ℤ :=
  ∑ p : V → Finset (Fin k),
    if (∀ v, (p v).card = 2) ∧ univ.biUnion p = univ then edgeSign G p else 0

/-- The graph invariant `ξ`. -/
noncomputable def ξ (G : SimpleGraph V) : ℚ :=
  (∑ k ∈ range (2 * Fintype.card V + 1), (-1 : ℚ) ^ k * (k + 1) * (T k G : ℚ)) /
    (-32 : ℚ) ^ Fintype.card V

end Graphs

/-- A rational graph invariant is a `4`-invariant if it is invariant under isomorphism
and satisfies the graph `4T` relations of Lando. -/
def IsFourInvariant (f : ∀ {V : Type} [Fintype V], SimpleGraph V → ℚ) : Prop :=
  (∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      Nonempty (G ≃g H) → f G = f H) ∧
  (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V), a ≠ b →
      f G - f (toggle G a b) = f (tilde G a b) - f (toggle (tilde G a b) a b))

end SL2W
