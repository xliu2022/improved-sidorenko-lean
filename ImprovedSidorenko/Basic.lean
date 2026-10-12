module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite simple uniform hypergraphs

The definitions in this file describe actual finite hypergraphs and injective
embeddings.  In particular, edge preservation alone is not called an embedding.
All averages later in the project are uniform averages over finite types.
-/

open scoped BigOperators

namespace ImprovedSidorenko

universe u v

/-- A simple r-uniform hypergraph with a finite edge set. The main statements
use finite vertex types Fin k. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace RGraph

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

/-- The paper requires global injectivity, including on isolated vertices. -/
def IsEmbedding (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

/-- A legal partial map is injective on the assigned set, whose image is a clique. -/
def Legal (H : RGraph W r) (A : Finset V) (φ : V → W) : Prop :=
  Set.InjOn φ (A : Set V) ∧
    ∀ e : Finset V, e ⊆ A → e.card = r → e.image φ ∈ H.edges

theorem legal_empty (H : RGraph W r) (hr : 0 < r) (φ : V → W) :
    H.Legal ∅ φ := by
  constructor
  · simp [Set.InjOn]
  · intro e he hc
    have : e = ∅ := Finset.subset_empty.mp he
    subst e
    simp at hc
    omega

theorem legal_completed_edge (F : RGraph V r) (H : RGraph W r)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {e : Finset V} (he : e ∈ F.edges) (hA : e ⊆ A) :
    e.image φ ∈ H.edges ∧ Set.InjOn φ (e : Set V) := by
  exact ⟨hφ.2 e hA (F.uniform e he), hφ.1.mono hA⟩

theorem legal_univ_isEmbedding [Fintype V] (F : RGraph V r) (H : RGraph W r)
    {φ : V → W} (hφ : H.Legal Finset.univ φ) : F.IsEmbedding H φ := by
  constructor
  · intro a b hab
    exact hφ.1 (by simp) (by simp) hab
  · intro e he
    exact hφ.2 e (Finset.subset_univ e) (F.uniform e he)

/-- Failure includes either an edge violation or a repeated image inside the edge. -/
noncomputable def edgeFailure (H : RGraph W r) (e : Finset V) (f : V → W) : ℝ := by
  classical
  exact if e.image f ∈ H.edges ∧ Set.InjOn f (e : Set V) then 0 else 1

theorem edgeFailure_nonneg (H : RGraph W r) (e : Finset V) (f : V → W) :
    0 ≤ H.edgeFailure e f := by
  classical
  unfold edgeFailure
  split_ifs <;> norm_num

theorem edgeFailure_le_one (H : RGraph W r) (e : Finset V) (f : V → W) :
    H.edgeFailure e f ≤ 1 := by
  classical
  unfold edgeFailure
  split_ifs <;> norm_num

theorem edgeFailure_eq_zero_iff (H : RGraph W r) (e : Finset V) (f : V → W) :
    H.edgeFailure e f = 0 ↔ e.image f ∈ H.edges ∧ Set.InjOn f (e : Set V) := by
  classical
  simp [edgeFailure]

theorem edgeFailure_congr (H : RGraph W r) (e : Finset V) {f g : V → W}
    (h : ∀ v ∈ e, f v = g v) : H.edgeFailure e f = H.edgeFailure e g := by
  classical
  have him : e.image f = e.image g := Finset.image_congr h
  have hinj : Set.InjOn f (e : Set V) ↔ Set.InjOn g (e : Set V) := by
    constructor
    · intro hf a ha b hb hab
      apply hf ha hb
      simpa only [h a ha, h b hb] using hab
    · intro hg a ha b hb hab
      apply hg ha hb
      simpa only [h a ha, h b hb] using hab
  simp only [edgeFailure, him, hinj]

/-- Every host edge belongs to the family of all `r`-subsets of its vertices. -/
theorem edge_card_le_choose {r n : ℕ} (H : RGraph (Fin n) r) :
    H.edges.card ≤ n.choose r := by
  classical
  have hsub : H.edges ⊆ (Finset.univ : Finset (Fin n)).powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, H.uniform e he⟩
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card hsub

end RGraph

/-- Use `φ` on assigned vertices and the independent random map `g` elsewhere. -/
def fill {V : Type u} {W : Type v} [DecidableEq V]
    (A : Finset V) (φ g : V → W) : V → W :=
  fun v => if v ∈ A then φ v else g v

@[simp] theorem fill_of_mem {V : Type u} {W : Type v} [DecidableEq V]
    (A : Finset V) (φ g : V → W) {v : V} (hv : v ∈ A) :
    fill A φ g v = φ v := by simp [fill, hv]

@[simp] theorem fill_of_not_mem {V : Type u} {W : Type v} [DecidableEq V]
    (A : Finset V) (φ g : V → W) {v : V} (hv : v ∉ A) :
    fill A φ g v = g v := by simp [fill, hv]

theorem fill_insert {V : Type u} {W : Type v} [DecidableEq V]
    (A : Finset V) (φ g : V → W) {v : V} (hv : v ∉ A) (x : W) :
    fill (insert v A) (Function.update φ v x) g =
      fill A φ (Function.update g v x) := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [fill, hv]
  · simp [fill, hw, Function.update_of_ne hw]

end ImprovedSidorenko
