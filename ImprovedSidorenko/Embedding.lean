module

public import ImprovedSidorenko.LegalChoices
public import ImprovedSidorenko.Completion
public import ImprovedSidorenko.Potential
public import ImprovedSidorenko.Iteration

@[expose] public section

/-!
# The two-stage finite embedding criterion

This file connects the actual hypergraph potentials, the legal-choice bound,
finite descent, the proved local lemma, and the collision estimate.  The input
is an explicit bound on the initial combined potential. `Main.lean` discharges
that bound using `Counting.lean` and the paper's explicit numerical constant.
-/

open scoped BigOperators

namespace ImprovedSidorenko

/-- Restricting a nonnegative random variable to a set of probability at least
`1-beta` increases its average by at most the factor `1/(1-beta)`. -/
theorem restricted_average_le {W : Type*} [Fintype W] [Nonempty W]
    (C : Finset W) (f : W → ℝ) (β : ℝ) (hβ : β < 1)
    (hC : 1 - β ≤ (C.card : ℝ) / (Fintype.card W : ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x ∈ C, f x) ≤ (𝔼 x : W, f x) / (1 - β) := by
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hcard := (le_div_iff₀ hn).mp hC
  have hnonneg : 0 ≤ 𝔼 x ∈ C, f x := Finset.expect_nonneg (fun x _ => hf x)
  have hsum : ∑ x ∈ C, f x ≤ ∑ x : W, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun x _ _ => hf x)
  have hsum' : (C.card : ℝ) * (𝔼 x ∈ C, f x) ≤
      (Fintype.card W : ℝ) * (𝔼 x : W, f x) := by
    simpa only [Finset.card_mul_expect, Fintype.card_mul_expect] using hsum
  have hmul := mul_le_mul_of_nonneg_right hcard hnonneg
  have hnorm : (1 - β) * (𝔼 x ∈ C, f x) ≤ 𝔼 x : W, f x := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith only [hmul, hsum']
  apply (le_div_iff₀ (by linarith : 0 < 1 - β)).mpr
  nlinarith only [hnorm]

namespace RGraph

universe u v
variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [Nonempty W] {r : ℕ}

noncomputable def totalPotential (F : RGraph V r) (H : RGraph W r)
    (T M : ℝ) (A : Finset V) (φ : V → W) : ℝ :=
  F.edgePotential H A φ + (r : ℝ) ^ 2 * M * H.cliquePotential T A φ

/-- Claim 2.2 with its probabilistic and legal-choice inputs proved from the
concrete definitions in this project. -/
theorem one_step_decreases (F : RGraph V r) (H : RGraph W r) (hr : 2 ≤ r)
    (T M β : ℝ) (hT : 0 < T) (hM : 0 < M) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (r : ℝ) - 4 * M / T)
    (hn : (Fintype.card V : ℝ) / (Fintype.card W : ℝ) ≤ β - 1 / (r : ℝ) ^ 2)
    (A : Finset V) (φ : V → W) (hlegal : H.Legal A φ)
    (hbudget : F.totalPotential H T M A φ ≤ M)
    (v : V) (hv : v ∉ A) (hload : 1 / (4 * (r : ℝ)) ≤ F.load H A φ v) :
    ∃ x : W, H.Legal (insert v A) (Function.update φ v x) ∧
      F.totalPotential H T M (insert v A) (Function.update φ v x) <
        F.totalPotential H T M A φ := by
  classical
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by linarith
  have hnW : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hβ1 : β < 1 := beta_lt_one hr' hM hT hβ
  have hΞ : H.cliquePotential T A φ ≤ 1 / (r : ℝ) ^ 2 :=
    clique_potential_le hrR hM (F.edgePotential_nonneg H A φ) hbudget
  let C := H.cliqueChoices A φ
  have hCratio : 1 - β ≤ (C.card : ℝ) / (Fintype.card W : ℝ) := by
    have hC := H.cliqueChoices_card_bound_by_potential hr0 hT.le A φ
    have hcard : (A.card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Finset.card_le_univ A
    have hcard' := div_le_div_of_nonneg_right hcard hnW.le
    dsimp [C]
    linarith
  have hCne : C.Nonempty := by
    apply Finset.card_pos.mp
    have hcp : (0 : ℝ) < C.card := by
      have h := (le_div_iff₀ hnW).mp hCratio
      nlinarith [mul_pos (show 0 < 1 - β by linarith) hnW]
    exact_mod_cast hcp
  let δ : W → ℝ := fun x =>
    H.cliquePotential T (insert v A) (Function.update φ v x) - H.cliquePotential T A φ
  let z : W → ℝ := fun x => F.updatedIncident H A φ v x + (r : ℝ) ^ 2 * M * δ x
  have hz0 : ∀ x, 0 ≤ z x := by
    intro x
    exact add_nonneg (F.updatedIncident_nonneg H A φ v x)
      (mul_nonneg (mul_nonneg (sq_nonneg _) hM.le)
        (H.cliquePotential_increment_nonneg hT.le A φ hv x))
  have hzavg : (𝔼 x : W, z x) ≤
      F.residualLoad H A φ v + (r : ℝ) ^ 2 * M * (H.cliquePotential T A φ / T) := by
    dsimp [z]
    rw [Finset.expect_add_distrib, ← Finset.mul_expect, F.expect_updatedIncident H A φ hv]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (H.cliquePotential_expected_increment_le hr0 hT A φ hv)
      (mul_nonneg (sq_nonneg _) hM.le)) _
  have hzC := (restricted_average_le C z β hβ1 hCratio hz0).trans
    (div_le_div_of_nonneg_right hzavg (by linarith))
  have hupdate (x : W) :
      F.totalPotential H T M (insert v A) (Function.update φ v x) =
        F.totalPotential H T M A φ - F.load H A φ v - F.residualLoad H A φ v + z x := by
    unfold totalPotential
    rw [F.edgePotential_update H A φ hv x]
    dsimp [z, δ]
    ring
  have havg : (𝔼 x ∈ C, F.totalPotential H T M (insert v A) (Function.update φ v x)) ≤
      F.totalPotential H T M A φ - F.load H A φ v - F.residualLoad H A φ v +
        F.residualLoad H A φ v / (1 - β) +
        (r : ℝ) ^ 2 * M * H.cliquePotential T A φ / (T * (1 - β)) := by
    simp_rw [hupdate]
    rw [Finset.expect_add_distrib, Finset.expect_const hCne]
    have h := add_le_add_right hzC
      (F.totalPotential H T M A φ - F.load H A φ v - F.residualLoad H A φ v)
    convert h using 1 <;>
      field_simp [hT.ne', (sub_pos.mpr hβ1).ne'] <;> ring
  have hweighted : (r : ℝ) ^ 2 * M * H.cliquePotential T A φ ≤ M := by
    have hPhi := F.edgePotential_nonneg H A φ
    unfold totalPotential at hbudget
    linarith
  have hstrict := one_step_strict_descent_of_raw_bound hr' hM hT hβ0 hβ hload
    (F.residualLoad_le H A φ v (by omega)) hweighted havg
  obtain ⟨x, hx, hdec⟩ := Finset.exists_lt_of_expect_lt hCne hstrict
  exact ⟨x, H.legal_insert_of_cliqueChoice hlegal hv
    ((H.mem_cliqueChoices A φ x).mp hx), hdec⟩

/-- Claim 2.3 for actual partial maps, using the number of unassigned vertices
as the decreasing natural-number rank. -/
theorem exists_small_load_partial_map (F : RGraph V r) (H : RGraph W r) (hr : 2 ≤ r)
    (T M β : ℝ) (hT : 0 < T) (hM : 0 < M) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (r : ℝ) - 4 * M / T)
    (hn : (Fintype.card V : ℝ) / (Fintype.card W : ℝ) ≤ β - 1 / (r : ℝ) ^ 2)
    (φ₀ : V → W) (hinit : F.totalPotential H T M ∅ φ₀ < M) :
    ∃ A : Finset V, ∃ φ : V → W, H.Legal A φ ∧ F.totalPotential H T M A φ < M ∧
      ∀ v, v ∉ A → F.load H A φ v < 1 / (4 * (r : ℝ)) := by
  classical
  let rank : (Finset V × (V → W)) → ℕ := fun s => (Finset.univ \ s.1).card
  have h := small_load_state rank (fun s => H.Legal s.1 s.2)
    (fun s => F.totalPotential H T M s.1 s.2)
    (fun s v => v ∉ s.1) (fun s v => F.load H s.1 s.2 v)
    M (1 / (4 * (r : ℝ)))
    (by
      intro s hs hp hex
      obtain ⟨v, hv, hl⟩ := hex
      obtain ⟨x, hleg, hdec⟩ := F.one_step_decreases H hr T M β hT hM hβ0 hβ hn
        s.1 s.2 hs hp.le v hv hl
      refine ⟨(insert v s.1, Function.update s.2 v x), hleg, hdec, ?_⟩
      dsimp [rank]
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩)]
      have hp := Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
      omega)
    (∅, φ₀) (H.legal_empty (by omega) φ₀) hinit
  obtain ⟨⟨A, φ⟩, hleg, hpot, hload⟩ := h
  exact ⟨A, φ, hleg, hpot, hload⟩

/-- A verified two-stage finite embedding criterion. `Main.lean` derives its
initial-potential hypothesis from the paper's edge-count density deficit.
It includes both the greedy potential stage and the probabilistic completion.
-/
theorem embedding_of_initial_potential (F : RGraph V r) (H : RGraph W r) (hr : 2 ≤ r)
    (T M β : ℝ) (hT : 0 < T) (hM : 0 < M) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (r : ℝ) - 4 * M / T)
    (hn : (Fintype.card V : ℝ) / (Fintype.card W : ℝ) ≤ β - 1 / (r : ℝ) ^ 2)
    (φ₀ : V → W) (hinit : F.totalPotential H T M ∅ φ₀ < M)
    (hcollision : ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) <
      (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card) :
    ∃ f : V → W, F.IsEmbedding H f := by
  obtain ⟨A, φ, hlegal, _, hload⟩ := F.exists_small_load_partial_map H hr T M β
    hT hM hβ0 hβ hn φ₀ hinit
  exact F.embedding_from_small_load H (by omega) A φ hlegal hload hcollision

end RGraph
end ImprovedSidorenko
