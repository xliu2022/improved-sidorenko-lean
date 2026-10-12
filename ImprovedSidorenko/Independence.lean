module

public import ImprovedSidorenko.Collision

@[expose] public section

/-!
# Independence from disjoint sets of random coordinates

The proof uses a coordinate-swap involution on a pair of independent uniform
maps. This verifies the dependency-graph condition required by the local lemma,
including independence from an entire collection of non-neighbours.
-/

open scoped BigOperators

namespace ImprovedSidorenko

universe u v

variable {V : Type u} {W : Type v} [DecidableEq V]

/-- An event is determined by its coordinates in `S`. -/
def EventSupported (P : (V → W) → Prop) (S : Finset V) : Prop :=
  ∀ f g, (∀ v ∈ S, f v = g v) → (P f ↔ P g)

/-- Exchange all coordinates outside `S` between two maps. -/
def swapOutside (S : Finset V) (p : (V → W) × (V → W)) :
    (V → W) × (V → W) :=
  (fill S p.1 p.2, fill S p.2 p.1)

theorem swapOutside_involutive (S : Finset V) :
    Function.Involutive (swapOutside (W := W) S) := by
  intro p
  apply Prod.ext <;> funext v <;> by_cases hv : v ∈ S <;> simp [swapOutside, fill, hv]

variable [Fintype V] [Fintype W] [Nonempty W]

/-- Factorization of the expectation of two functions on disjoint coordinates. -/
theorem expect_mul_of_disjoint_support
    (f g : (V → W) → ℝ) (S T : Finset V) (hST : Disjoint S T)
    (hf : ∀ a b, (∀ v ∈ S, a v = b v) → f a = f b)
    (hg : ∀ a b, (∀ v ∈ T, a v = b v) → g a = g b) :
    (𝔼 a : V → W, f a * g a) = (𝔼 a, f a) * (𝔼 a, g a) := by
  classical
  let e : ((V → W) × (V → W)) ≃ ((V → W) × (V → W)) :=
    ⟨swapOutside S, swapOutside S, swapOutside_involutive S, swapOutside_involutive S⟩
  have h := Fintype.expect_equiv e
    (fun p : (V → W) × (V → W) => f p.1 * g p.2)
    (fun p : (V → W) × (V → W) => f p.1 * g p.1)
    (by
      intro p
      change f p.1 * g p.2 = f (fill S p.1 p.2) * g (fill S p.1 p.2)
      have hf' : f (fill S p.1 p.2) = f p.1 := by
        apply hf
        intro v hv
        simp [fill, hv]
      have hg' : g (fill S p.1 p.2) = g p.2 := by
        apply hg
        intro v hv
        have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hST h hv
        simp [fill, hvS]
      rw [hf', hg'])
  simp only [← Finset.univ_product_univ, Finset.expect_product,
    Fintype.expect_const] at h
  rw [← Fintype.expect_mul_expect] at h
  exact h.symm

/-- Independence of finite uniform events with disjoint coordinate supports. -/
theorem eventProb_inter_of_disjoint_support
    (P Q : (V → W) → Prop) (S T : Finset V) (hST : Disjoint S T)
    (hP : EventSupported P S) (hQ : EventSupported Q T) :
    eventProb (fun g : V → W => P g ∧ Q g) = eventProb P * eventProb Q := by
  classical
  have hind := expect_mul_of_disjoint_support
    (fun a => if P a then (1 : ℝ) else 0)
    (fun a => if Q a then (1 : ℝ) else 0) S T hST
    (by intro a b hab; rw [hP a b hab])
    (by intro a b hab; rw [hQ a b hab])
  calc
    eventProb (fun g : V → W => P g ∧ Q g) =
        𝔼 a : V → W, ((if P a then (1 : ℝ) else 0) *
          (if Q a then (1 : ℝ) else 0)) := by
      unfold eventProb
      apply Finset.expect_congr rfl
      intro a _
      dsimp only
      by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq]
    _ = eventProb P * eventProb Q := hind

theorem EventSupported.not {P : (V → W) → Prop} {S : Finset V}
    (h : EventSupported P S) : EventSupported (fun a => ¬ P a) S := by
  intro a b hab
  exact not_congr (h a b hab)

/-- A collection of events is determined by the union of all its supports. -/
theorem EventSupported.forall_finset {I : Type*} (s : Finset I)
    (P : I → (V → W) → Prop) (support : I → Finset V)
    (h : ∀ i ∈ s, EventSupported (P i) (support i)) :
    EventSupported (fun a => ∀ i ∈ s, P i a) (s.biUnion support) := by
  classical
  intro a b hab
  constructor
  · intro ha i hi
    apply (h i hi a b (fun v hv => hab v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩))).mp
    exact ha i hi
  · intro hb i hi
    apply (h i hi a b (fun v hv => hab v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩))).mpr
    exact hb i hi

namespace RGraph

variable [DecidableEq W] {r : ℕ}

def badEvent (H : RGraph W r) (A : Finset V) (φ : V → W) (e : Finset V)
    (g : V → W) : Prop :=
  ¬ (e.image (fill A φ g) ∈ H.edges ∧ Set.InjOn (fill A φ g) (e : Set V))

/-- The bad event used in the LLL has exactly the conditional failure probability. -/
theorem badEvent_probability (H : RGraph W r) (A : Finset V)
    (φ : V → W) (e : Finset V) :
    eventProb (H.badEvent A φ e) = H.failureProb A φ e := by
  classical
  unfold eventProb failureProb badEvent edgeFailure
  apply Finset.expect_congr rfl
  intro g _
  split_ifs <;> simp_all

/-- An unfinished edge failure depends only on its unassigned vertices. -/
theorem badEvent_supported (H : RGraph W r) (A : Finset V)
    (φ : V → W) (e : Finset V) : EventSupported (H.badEvent A φ e) (e \ A) := by
  intro g h hgh
  have hfill : ∀ v ∈ e, fill A φ g v = fill A φ h v := by
    intro v hv
    by_cases hvA : v ∈ A
    · simp [fill, hvA]
    · simp only [fill, ite_eq_right hvA]
      exact hgh v (Finset.mem_sdiff.mpr ⟨hv, hvA⟩)
  have heq := H.edgeFailure_congr e hfill
  have hz := congrArg (fun x : ℝ => x = 0) heq
  rw [H.edgeFailure_eq_zero_iff, H.edgeFailure_eq_zero_iff] at hz
  exact not_congr (Iff.of_eq hz)

end RGraph
end ImprovedSidorenko
