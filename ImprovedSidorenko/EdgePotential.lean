module

public import ImprovedSidorenko.Conditional

@[expose] public section

/-!
# The unfinished-edge potential

This file implements the probabilities using actual finite uniform maps from
`Conditional.lean`. Claims 2.1(i) and 2.1(iii) therefore do not take the tower
law or the update formula as hypotheses.
-/

open scoped BigOperators

namespace ImprovedSidorenko
namespace RGraph

universe u v

variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [Nonempty W] {r : ℕ}

/-- Number of unassigned vertices in an edge. -/
def remaining (A e : Finset V) : ℕ := (e \ A).card

noncomputable def edgePotential (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) : ℝ :=
  ∑ e ∈ F.edges, (remaining A e : ℝ) * H.failureProb A φ e

noncomputable def load (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) : ℝ :=
  ∑ e ∈ F.edges, if v ∈ e then H.failureProb A φ e else 0

noncomputable def residualLoad (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) : ℝ :=
  ∑ e ∈ F.edges,
    if v ∈ e then ((remaining A e - 1 : ℕ) : ℝ) * H.failureProb A φ e else 0

noncomputable def updatedIncident (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) (x : W) : ℝ :=
  ∑ e ∈ F.edges,
    if v ∈ e then ((remaining A e - 1 : ℕ) : ℝ) *
      H.failureProb (insert v A) (Function.update φ v x) e else 0

theorem remaining_le (F : RGraph V r) (A : Finset V)
    {e : Finset V} (he : e ∈ F.edges) : remaining A e ≤ r := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans (F.uniform e he).le

theorem remaining_pos {A e : Finset V} {v : V} (hv : v ∉ A) (he : v ∈ e) :
    1 ≤ remaining A e := by
  exact Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨he, hv⟩⟩

theorem remaining_insert_of_mem (A e : Finset V) {v : V}
    (hv : v ∉ A) (he : v ∈ e) :
    remaining (insert v A) e = remaining A e - 1 := by
  exact (congrArg Finset.card (Finset.sdiff_insert e A v)).trans
    (Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨he, hv⟩))

theorem remaining_insert_of_not_mem (A e : Finset V) {v : V} (he : v ∉ e) :
    remaining (insert v A) e = remaining A e := by
  unfold remaining
  congr 1
  ext w
  by_cases hw : w = v
  · subst w; simp [he]
  · simp [hw]

theorem edgePotential_nonneg (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) : 0 ≤ F.edgePotential H A φ := by
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (Nat.cast_nonneg _)
    (H.failureProb_nonneg A φ e))

theorem load_nonneg (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) : 0 ≤ F.load H A φ v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact H.failureProb_nonneg A φ e
  · exact le_rfl

theorem updatedIncident_nonneg (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) (x : W) :
    0 ≤ F.updatedIncident H A φ v x := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (H.failureProb_nonneg _ _ e)
  · exact le_rfl

/-- Claim 2.1(i), including the exact expectation identity. -/
theorem expect_updatedIncident (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) :
    (𝔼 x : W, F.updatedIncident H A φ v x) = F.residualLoad H A φ v := by
  unfold updatedIncident residualLoad
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : v ∈ e
  · simp only [ite_eq_left he, ← Finset.mul_expect, H.failureProb_tower A φ e hv]
  · simp only [ite_eq_right he, Fintype.expect_const]

theorem residualLoad_le (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) (hr : 1 ≤ r) :
    F.residualLoad H A φ v ≤ ((r : ℝ) - 1) * F.load H A φ v := by
  unfold residualLoad load
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases hv : v ∈ e
  · simp only [ite_eq_left hv]
    apply mul_le_mul_of_nonneg_right _ (H.failureProb_nonneg A φ e)
    calc
      ((remaining A e - 1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le_sub_right (F.remaining_le A he) 1
      _ = (r : ℝ) - 1 := by rw [Nat.cast_sub hr]; norm_num
  · simp only [ite_eq_right hv, mul_zero, le_refl]

/-- Claim 2.1(iii). It is valid even if the next assignment is illegal. -/
theorem edgePotential_update (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) (x : W) :
    F.edgePotential H (insert v A) (Function.update φ v x) =
      F.edgePotential H A φ - F.load H A φ v - F.residualLoad H A φ v +
        F.updatedIncident H A φ v x := by
  unfold edgePotential load residualLoad updatedIncident
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : v ∈ e
  · simp only [ite_eq_left he, remaining_insert_of_mem A e hv he]
    have hs : (((remaining A e - 1 : ℕ)) : ℝ) = (remaining A e : ℝ) - 1 := by
      rw [Nat.cast_sub (remaining_pos hv he)]
      norm_num
    rw [hs]
    ring
  · simp only [ite_eq_right he, remaining_insert_of_not_mem A e he,
      H.failureProb_update_of_not_mem A φ e hv he x, sub_zero, add_zero]

/-- The edge potential is exactly the sum of the unassigned vertex loads. -/
theorem edgePotential_eq_sum_load (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) :
    F.edgePotential H A φ = ∑ v ∈ Finset.univ \ A, F.load H A φ v := by
  classical
  unfold edgePotential load
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hset : (Finset.univ \ A).filter (fun v => v ∈ e) = e \ A := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  rw [← Finset.sum_filter, hset]
  simp [remaining, nsmul_eq_mul]

end RGraph
end ImprovedSidorenko
