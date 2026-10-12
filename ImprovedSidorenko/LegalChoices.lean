module

public import ImprovedSidorenko.CliquePotential

@[expose] public section

/-!
# Proportion of legal host choices

This file bounds the actual finite set of legal one-vertex extensions using the
clique failure kernels. The pointwise union bound is averaged over independent
uniform host choices, giving Claim 2.1(iv) in the manuscript.
-/

open scoped BigOperators

namespace ImprovedSidorenko
namespace RGraph

universe u v
variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype W] {r : ℕ}

/-- A host choice is unused and succeeds with every relevant old subset. -/
def IsCliqueChoice (H : RGraph W r) (A : Finset V) (φ : V → W) (x : W) : Prop :=
  x ∉ A.image φ ∧ ∀ I ∈ A.powersetCard (r - 1),
    H.cliqueKernel 0 (x :: I.toList.map φ) = 0

/-- Every clique choice extends a legal partial map to another legal map. -/
theorem legal_insert_of_cliqueChoice (H : RGraph W r)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {v : V} (_hv : v ∉ A) {x : W} (hx : H.IsCliqueChoice A φ x) :
    H.Legal (insert v A) (Function.update φ v x) := by
  classical
  constructor
  · intro a ha b hb hab
    by_cases hav : a = v
    · subst a
      by_cases hbv : b = v
      · exact hbv.symm
      · have hbA : b ∈ A := (Finset.mem_insert.mp hb).resolve_left hbv
        have hxb : x = φ b := by simpa [Function.update_of_ne hbv] using hab
        exact False.elim (hx.1 (Finset.mem_image.mpr ⟨b, hbA, hxb.symm⟩))
    · by_cases hbv : b = v
      · subst b
        have haA : a ∈ A := (Finset.mem_insert.mp ha).resolve_left hav
        have hax : φ a = x := by simpa [Function.update_of_ne hav] using hab
        exact False.elim (hx.1 (Finset.mem_image.mpr ⟨a, haA, hax⟩))
      · apply hφ.1 ((Finset.mem_insert.mp ha).resolve_left hav)
          ((Finset.mem_insert.mp hb).resolve_left hbv)
        simpa [Function.update_of_ne hav, Function.update_of_ne hbv] using hab
  · intro e he hecard
    by_cases hve : v ∈ e
    · let I := e.erase v
      have hIA : I ⊆ A := by
        intro w hw
        have hw' := Finset.mem_erase.mp hw
        exact (Finset.mem_insert.mp (he hw'.2)).resolve_left hw'.1
      have hIcard : I.card = r - 1 := by
        dsimp [I]
        rw [Finset.card_erase_of_mem hve, hecard]
      have hI : I ∈ A.powersetCard (r - 1) := Finset.mem_powersetCard.mpr ⟨hIA, hIcard⟩
      have hed := (H.cliqueKernel_zero_eq_zero_iff _).mp (hx.2 I hI)
      have him : I.image (Function.update φ v x) = I.image φ := by
        apply Finset.image_congr
        intro w hw
        exact Function.update_of_ne (Finset.mem_erase.mp hw).1 x φ
      have hins : insert v I = e := Finset.insert_erase hve
      have heimage : e.image (Function.update φ v x) =
          (x :: I.toList.map φ).toFinset := by
        rw [← hins, Finset.image_insert, Function.update_self, him]
        ext w
        simp
      rw [heimage]
      exact hed.2
    · have heA : e ⊆ A := by
        intro w hw
        have hwv : w ≠ v := by intro h; exact hve (h ▸ hw)
        exact (Finset.mem_insert.mp (he hw)).resolve_left hwv
      have him : e.image (Function.update φ v x) = e.image φ := by
        apply Finset.image_congr
        intro w hw
        have hwv : w ≠ v := by intro h; exact hve (h ▸ hw)
        exact Function.update_of_ne hwv x φ
      rw [him]
      exact hφ.2 e heA hecard

/-- The finite set of host choices satisfying the clique extension conditions. -/
noncomputable def cliqueChoices (H : RGraph W r) (A : Finset V) (φ : V → W) : Finset W := by
  classical
  exact Finset.univ.filter (H.IsCliqueChoice A φ)

omit [DecidableEq V] in
@[simp] theorem mem_cliqueChoices (H : RGraph W r) (A : Finset V) (φ : V → W) (x : W) :
    x ∈ H.cliqueChoices A φ ↔ H.IsCliqueChoice A φ x := by
  classical
  simp [cliqueChoices]

omit [DecidableEq V] in
/-- Pointwise union bound for the host vertices excluded by the clique condition. -/
theorem cliqueChoice_failure_indicator_le (H : RGraph W r)
    (A : Finset V) (φ : V → W) (x : W) :
    (if x ∈ H.cliqueChoices A φ then (0 : ℝ) else 1) ≤
      (if x ∈ A.image φ then (1 : ℝ) else 0) +
      ∑ I ∈ A.powersetCard (r - 1), H.cliqueKernel 0 (x :: I.toList.map φ) := by
  classical
  have hsum : 0 ≤ ∑ I ∈ A.powersetCard (r - 1),
      H.cliqueKernel 0 (x :: I.toList.map φ) :=
    Finset.sum_nonneg (fun I _ => H.cliqueKernel_nonneg _ _)
  by_cases hgood : x ∈ H.cliqueChoices A φ
  · simp only [ite_eq_left hgood]
    split_ifs <;> linarith
  · simp only [ite_eq_right hgood]
    by_cases hused : x ∈ A.image φ
    · simp only [ite_eq_left hused]
      linarith
    · simp only [ite_eq_right hused, zero_add]
      have hbad : ∃ I ∈ A.powersetCard (r - 1),
          H.cliqueKernel 0 (x :: I.toList.map φ) ≠ 0 := by
        by_contra h
        push Not at h
        exact hgood ((H.mem_cliqueChoices A φ x).mpr ⟨hused, h⟩)
      obtain ⟨I, hI, hfail⟩ := hbad
      have hone := H.cliqueKernel_zero_eq_one_of_ne_zero _ hfail
      calc
        (1 : ℝ) = H.cliqueKernel 0 (x :: I.toList.map φ) := hone.symm
        _ ≤ ∑ J ∈ A.powersetCard (r - 1), H.cliqueKernel 0 (x :: J.toList.map φ) :=
          Finset.single_le_sum
            (f := fun J : Finset V => H.cliqueKernel 0 (x :: J.toList.map φ))
            (fun J _ => H.cliqueKernel_nonneg _ _) hI

omit [DecidableEq V] in
/-- The top unweighted summand is bounded by the whole clique potential. -/
theorem cliqueSum_top_le_potential (H : RGraph W r) (hr : 0 < r)
    {T : ℝ} (hT : 0 ≤ T) (A : Finset V) (φ : V → W) :
    H.cliqueSum A φ (r - 1) ≤ H.cliquePotential T A φ := by
  have hmem : r - 1 ∈ Finset.range r := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum
    (f := fun j => T ^ (r - 1 - j) * H.cliqueSum A φ j)
    (fun j _ => mul_nonneg (pow_nonneg hT _) (H.cliqueSum_nonneg A φ j)) hmem
  simpa [cliquePotential] using h

/-- Uniform expectation of a finite-set membership indicator. -/
theorem expect_membership_indicator (B : Finset W) :
    (𝔼 x : W, if x ∈ B then (1 : ℝ) else 0) =
      (B.card : ℝ) / Fintype.card W := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  have hfilter : Finset.univ.filter (fun x : W => x ∈ B) = B := by ext x; simp
  simp [hfilter]

theorem expect_nonmembership_indicator [Nonempty W] (B : Finset W) :
    (𝔼 x : W, if x ∈ B then (0 : ℝ) else 1) =
      1 - (B.card : ℝ) / Fintype.card W := by
  classical
  calc
    (𝔼 x : W, if x ∈ B then (0 : ℝ) else 1)
        = 𝔼 x : W, ((1 : ℝ) - (if x ∈ B then (1 : ℝ) else 0)) := by
          apply Finset.expect_congr rfl
          intro x _
          split_ifs <;> norm_num
    _ = 1 - (B.card : ℝ) / Fintype.card W := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const, expect_membership_indicator]

omit [DecidableEq V] in
/-- At most `|A|/|W| + S_{r-1}` of the host vertices are excluded.
The inequality uses `card (A.image φ) ≤ card A`, so it does not need injectivity
as an additional assumption. -/
theorem cliqueChoices_card_bound [Nonempty W] (H : RGraph W r) (hr : 0 < r)
    (A : Finset V) (φ : V → W) :
    1 - (A.card : ℝ) / Fintype.card W - H.cliqueSum A φ (r - 1) ≤
      ((H.cliqueChoices A φ).card : ℝ) / Fintype.card W := by
  classical
  have h := Finset.expect_le_expect
    (s := (Finset.univ : Finset W)) (fun x _ => H.cliqueChoice_failure_indicator_le A φ x)
  rw [expect_nonmembership_indicator, Finset.expect_add_distrib,
    expect_membership_indicator, Finset.expect_sum_comm] at h
  have hmean : (∑ I ∈ A.powersetCard (r - 1),
      𝔼 x : W, H.cliqueKernel 0 (x :: I.toList.map φ)) = H.cliqueSum A φ (r - 1) := by
    unfold cliqueSum
    apply Finset.sum_congr rfl
    intro I hI
    have hk : r - (r - 1) = 1 := by omega
    rw [hk, cliqueKernel_succ]
  rw [hmean] at h
  have hcard : ((A.image φ).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_image_le
  have hdiv := div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ Fintype.card W)
  linarith

omit [DecidableEq V] in
/-- Claim 2.1(iv), for the explicitly constructed set of legal clique choices. -/
theorem cliqueChoices_card_bound_by_potential [Nonempty W]
    (H : RGraph W r) (hr : 0 < r) {T : ℝ} (hT : 0 ≤ T)
    (A : Finset V) (φ : V → W) :
    1 - (A.card : ℝ) / Fintype.card W - H.cliquePotential T A φ ≤
      ((H.cliqueChoices A φ).card : ℝ) / Fintype.card W := by
  have h := H.cliqueChoices_card_bound hr A φ
  have htop := H.cliqueSum_top_le_potential hr hT A φ
  linarith

/-- Membership in the explicit safe set is enough to preserve legality. -/
theorem legal_of_mem_cliqueChoices (H : RGraph W r)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {v : V} (hv : v ∉ A) {x : W} (hx : x ∈ H.cliqueChoices A φ) :
    H.Legal (insert v A) (Function.update φ v x) := by
  exact H.legal_insert_of_cliqueChoice hφ hv ((H.mem_cliqueChoices A φ x).mp hx)

/-- All host vertices which actually give a legal one-vertex extension. -/
noncomputable def legalChoices (H : RGraph W r) (A : Finset V)
    (φ : V → W) (v : V) : Finset W := by
  classical
  exact Finset.univ.filter (fun x => H.Legal (insert v A) (Function.update φ v x))

@[simp] theorem mem_legalChoices (H : RGraph W r) (A : Finset V)
    (φ : V → W) (v : V) (x : W) :
    x ∈ H.legalChoices A φ v ↔ H.Legal (insert v A) (Function.update φ v x) := by
  classical
  simp [legalChoices]

/-- The explicit safe set consists of actual legal extensions. -/
theorem cliqueChoices_subset_legalChoices (H : RGraph W r)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {v : V} (hv : v ∉ A) : H.cliqueChoices A φ ⊆ H.legalChoices A φ v := by
  classical
  intro x hx
  exact (H.mem_legalChoices A φ v x).mpr (H.legal_of_mem_cliqueChoices hφ hv hx)

/-- Claim 2.1(iv) for the set of all actual legal one-vertex extensions. -/
theorem legalChoices_card_bound_by_potential [Nonempty W]
    (H : RGraph W r) (hr : 0 < r) {T : ℝ} (hT : 0 ≤ T)
    {A : Finset V} {φ : V → W} (hφ : H.Legal A φ)
    {v : V} (hv : v ∉ A) :
    1 - (A.card : ℝ) / Fintype.card W - H.cliquePotential T A φ ≤
      ((H.legalChoices A φ v).card : ℝ) / Fintype.card W := by
  have hcard : ((H.cliqueChoices A φ).card : ℝ) ≤ (H.legalChoices A φ v).card := by
    exact_mod_cast Finset.card_le_card (H.cliqueChoices_subset_legalChoices hφ hv)
  exact (H.cliqueChoices_card_bound_by_potential hr hT A φ).trans
    (div_le_div_of_nonneg_right hcard (by positivity))


end RGraph
end ImprovedSidorenko
