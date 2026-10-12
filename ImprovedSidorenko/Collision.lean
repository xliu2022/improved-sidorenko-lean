module

public import ImprovedSidorenko.Conditional
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# Removing collisions after preserving edges

This is the final finite-probability argument in the paper. The exact
`choose(v(F), 2) / n` error is proved for the actual independent extension of
an injective partial map; pairwise independence of the collision events is
neither assumed nor needed.
-/

open scoped BigOperators

namespace ImprovedSidorenko

universe u v w

/-- Probability of an event in a finite uniform sample space. -/
noncomputable def eventProb {Ω : Type u} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact 𝔼 ω : Ω, if P ω then (1 : ℝ) else 0

theorem eventProb_congr {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : eventProb P = eventProb Q := by
  classical
  simp only [eventProb, h]

theorem eventProb_nonneg {Ω : Type u} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ eventProb P := by
  classical
  apply Finset.expect_nonneg
  intro ω _
  split_ifs <;> norm_num

theorem eventProb_mono {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ ω, P ω → Q ω) : eventProb P ≤ eventProb Q := by
  classical
  apply Finset.expect_le_expect
  intro ω _
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [ite_eq_right hp]
    split_ifs <;> norm_num

/-- The elementary finite union bound, with overlaps allowed. -/
theorem eventProb_union_bound {Ω : Type u} {I : Type v} [Fintype Ω]
    (s : Finset I) (P : I → Ω → Prop) :
    eventProb (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, eventProb (P i) := by
  classical
  unfold eventProb
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro ω _
  dsimp only
  by_cases h : ∃ i ∈ s, P i ω
  · rw [ite_eq_left h]
    obtain ⟨i, hi, hp⟩ := h
    calc
      (1 : ℝ) = (if P i ω then 1 else 0) := by simp [hp]
      _ ≤ ∑ j ∈ s, if P j ω then (1 : ℝ) else 0 := by
        exact Finset.single_le_sum (f := fun j => if P j ω then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

/-- Positive probability survives deleting a smaller exceptional event. -/
theorem exists_good_not_bad {Ω : Type u} [Fintype Ω] (Good Bad : Ω → Prop)
    (h : eventProb Bad < eventProb Good) : ∃ ω, Good ω ∧ ¬ Bad ω := by
  classical
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (eventProb_mono hn)) h

section Collision

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] [Nonempty W]

/-- A specified collision with at least one fresh endpoint has probability exactly `1/n`. -/
theorem collision_probability (A : Finset V) (φ : V → W) {a b : V}
    (ha : a ∉ A) (hab : a ≠ b) :
    eventProb (fun g : V → W => fill A φ g a = fill A φ g b) =
      1 / (Fintype.card W : ℝ) := by
  classical
  unfold eventProb
  dsimp only
  rw [← expect_resample _ a]
  rw [Finset.expect_comm]
  have hba : b ≠ a := Ne.symm hab
  have hfill (g : V → W) (x : W) : fill A φ (Function.update g a x) b = fill A φ g b := by
    simp [fill, Function.update_of_ne hba]
  simp only [fill_of_not_mem A φ _ ha, Function.update_self, hfill]
  have hone (y : W) : (𝔼 x : W, if x = y then (1 : ℝ) else 0) =
      1 / (Fintype.card W : ℝ) := by
    simp [Fintype.expect_eq_sum_div_card]
  simp only [hone, Fintype.expect_const]

theorem collision_probability_le (A : Finset V) (φ : V → W)
    (hinj : Set.InjOn φ (A : Set V)) {a b : V} (hab : a ≠ b) :
    eventProb (fun g : V → W => fill A φ g a = fill A φ g b) ≤
      1 / (Fintype.card W : ℝ) := by
  classical
  by_cases ha : a ∈ A
  · by_cases hb : b ∈ A
    · have hne : φ a ≠ φ b := fun h => hab (hinj ha hb h)
      have hzero : eventProb (fun g : V → W => fill A φ g a = fill A φ g b) = 0 := by
        simp [eventProb, fill, ha, hb, hne]
      rw [hzero]
      positivity
    · rw [eventProb_congr (fun g => eq_comm)]
      exact (collision_probability A φ hb hab.symm).le
  · exact (collision_probability A φ ha hab).le

theorem noninjective_iff_pair (f : V → W) :
    ¬ Function.Injective f ↔
      ∃ e ∈ (Finset.univ : Finset V).powersetCard 2,
        ¬ Set.InjOn f (e : Set V) := by
  classical
  constructor
  · intro hn
    have hex : ∃ a b, f a = f b ∧ a ≠ b := by
      unfold Function.Injective at hn
      push Not at hn
      exact hn
    obtain ⟨a, b, heq, hne⟩ := hex
    refine ⟨{a, b}, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, Finset.card_pair hne⟩, ?_⟩
    intro hi
    exact hne (hi (by simp) (by simp) heq)
  · rintro ⟨e, _, hn⟩ hi
    exact hn (hi.injOn)

/-- The exact collision error in the manuscript. -/
theorem noninjective_probability_le (A : Finset V) (φ : V → W)
    (hinj : Set.InjOn φ (A : Set V)) :
    eventProb (fun g : V → W => ¬ Function.Injective (fill A φ g)) ≤
      ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
  classical
  rw [eventProb_congr (fun g => noninjective_iff_pair (fill A φ g))]
  calc
    eventProb (fun g : V → W => ∃ e ∈ (Finset.univ : Finset V).powersetCard 2,
        ¬ Set.InjOn (fill A φ g) (e : Set V))
      ≤ ∑ e ∈ (Finset.univ : Finset V).powersetCard 2,
          eventProb (fun g : V → W => ¬ Set.InjOn (fill A φ g) (e : Set V)) :=
        eventProb_union_bound _ _
    _ ≤ ∑ _e ∈ (Finset.univ : Finset V).powersetCard 2,
          1 / (Fintype.card W : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp he).2
      have heq : ∀ g : V → W,
          (¬ Set.InjOn (fill A φ g) (({a, b} : Finset V) : Set V)) ↔
            fill A φ g a = fill A φ g b := by
        intro g
        simp [Set.injOn_pair, hab]
      rw [eventProb_congr heq]
      exact collision_probability_le A φ hinj hab
    _ = ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
      simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Once the edge-success probability beats the proved collision bound, a copy exists. -/
theorem embedding_of_success_probability {r : ℕ} (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (hinj : Set.InjOn φ (A : Set V))
    (hsuccess : ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) <
      eventProb (fun g : V → W => ∀ e ∈ F.edges, (e.image (fill A φ g)) ∈ H.edges)) :
    ∃ f : V → W, F.IsEmbedding H f := by
  have hlt := lt_of_le_of_lt (noninjective_probability_le A φ hinj) hsuccess
  obtain ⟨g, hg, hi⟩ := exists_good_not_bad
    (fun g : V → W => ∀ e ∈ F.edges, (e.image (fill A φ g)) ∈ H.edges)
    (fun g : V → W => ¬ Function.Injective (fill A φ g)) hlt
  exact ⟨fill A φ g, not_not.mp hi, hg⟩

end Collision
end ImprovedSidorenko
