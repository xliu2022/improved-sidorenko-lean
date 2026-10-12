module

public import ImprovedSidorenko.Basic
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
# Conditional failure probabilities from independent uniform maps

The tower identity here is proved by an explicit involution on the finite
sample space. It is not assumed as a field of an abstract probability object.
Sampling an entire map and then ignoring its assigned coordinates gives the
same uniform distribution on the remaining coordinates.
-/

open scoped BigOperators

namespace ImprovedSidorenko

universe u v

section Resampling

variable {V : Type u} {W : Type v} [DecidableEq V]

/-- Swap an extra sample with the value of a random map at one coordinate. -/
def swapSample (v : V) (p : W × (V → W)) : W × (V → W) :=
  (p.2 v, Function.update p.2 v p.1)

theorem swapSample_involutive (v : V) : Function.Involutive (swapSample (W := W) v) := by
  intro p
  apply Prod.ext
  · simp [swapSample]
  · funext w
    by_cases hw : w = v
    · subst w
      simp [swapSample]
    · simp [swapSample, Function.update_of_ne hw]

variable [Fintype V] [Fintype W] [Nonempty W]

/-- Averaging a fresh value into one coordinate leaves the uniform average unchanged. -/
theorem expect_resample (f : (V → W) → ℝ) (v : V) :
    (𝔼 x : W, 𝔼 g : V → W, f (Function.update g v x)) = 𝔼 g, f g := by
  classical
  let e : (W × (V → W)) ≃ (W × (V → W)) :=
    ⟨swapSample v, swapSample v, swapSample_involutive v, swapSample_involutive v⟩
  have h := Fintype.expect_equiv e
    (fun p : W × (V → W) => f (Function.update p.2 v p.1))
    (fun p : W × (V → W) => f p.2) (fun _ => rfl)
  simp only [← Finset.univ_product_univ, Finset.expect_product] at h
  simpa only [Fintype.expect_const] using h

end Resampling

namespace RGraph

variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [Nonempty W] {r : ℕ}

/-- The actual conditional edge failure probability for a fixed partial map. -/
noncomputable def failureProb (H : RGraph W r) (A : Finset V) (φ : V → W)
    (e : Finset V) : ℝ :=
  𝔼 g : V → W, H.edgeFailure e (fill A φ g)

theorem failureProb_nonneg (H : RGraph W r) (A : Finset V) (φ : V → W)
    (e : Finset V) : 0 ≤ H.failureProb A φ e := by
  exact Finset.expect_nonneg (fun _ _ => H.edgeFailure_nonneg _ _)

theorem failureProb_le_one (H : RGraph W r) (A : Finset V) (φ : V → W)
    (e : Finset V) : H.failureProb A φ e ≤ 1 := by
  exact Finset.expect_le Finset.univ_nonempty (fun _ _ => H.edgeFailure_le_one _ _)

/-- Equation (2.4) in its coordinate form, valid also for an illegal next choice. -/
theorem failureProb_tower (H : RGraph W r) (A : Finset V) (φ : V → W)
    (e : Finset V) {v : V} (hv : v ∉ A) :
    (𝔼 x : W, H.failureProb (insert v A) (Function.update φ v x) e) =
      H.failureProb A φ e := by
  simp only [failureProb, fill_insert A φ _ hv]
  exact expect_resample (fun g => H.edgeFailure e (fill A φ g)) v

/-- An edge not meeting the new coordinate has unchanged conditional probability. -/
theorem failureProb_update_of_not_mem (H : RGraph W r) (A : Finset V)
    (φ : V → W) (e : Finset V) {v : V} (hv : v ∉ A) (he : v ∉ e) (x : W) :
    H.failureProb (insert v A) (Function.update φ v x) e = H.failureProb A φ e := by
  unfold failureProb
  apply Finset.expect_congr rfl
  intro g _
  apply H.edgeFailure_congr
  intro w hw
  have hwv : w ≠ v := by
    intro h
    exact he (h ▸ hw)
  rw [fill_insert A φ g hv x]
  simp [fill, Function.update_of_ne hwv]

/-- Legality really makes every completely assigned edge successful. -/
theorem failureProb_completed (F : RGraph V r) (H : RGraph W r)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {e : Finset V} (he : e ∈ F.edges) (hA : e ⊆ A) :
    H.failureProb A φ e = 0 := by
  unfold failureProb
  apply Finset.expect_eq_zero
  intro g _
  have hc := legal_completed_edge F H hφ he hA
  have hfail : H.edgeFailure e φ = 0 := (H.edgeFailure_eq_zero_iff e φ).2 hc
  calc
    H.edgeFailure e (fill A φ g) = H.edgeFailure e φ := by
      apply H.edgeFailure_congr
      intro w hw
      exact fill_of_mem A φ g (hA hw)
    _ = 0 := hfail

end RGraph

end ImprovedSidorenko
