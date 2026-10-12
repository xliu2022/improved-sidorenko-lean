module

public import ImprovedSidorenko.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Insert

@[expose] public section

/-!
# Actual conditional clique-failure kernels

The kernel in this file is defined by repeatedly averaging an independent
uniform host vertex.  Its terminal value tests both distinctness and membership
in the host edge set.  Consequently the tower identity is definitional, and
permutation invariance is proved from the edge test, not assumed.

`cliqueSum` is the paper's `S_j`, indexed by subsets of the assigned domain.
The insertion and averaged-increment lemmas establish the subset-counting part
of Claim 2.1(ii).
-/

open scoped BigOperators

namespace ImprovedSidorenko

namespace RGraph

universe u v

variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype W] {r : ℕ}

/-- Conditional failure when `s` more independent host vertices are to be
sampled and `l` is the list of host vertices already specified. -/
noncomputable def cliqueKernel (H : RGraph W r) : ℕ → List W → ℝ
  | 0, l => if l.Nodup ∧ l.toFinset ∈ H.edges then 0 else 1
  | s + 1, l => 𝔼 x : W, H.cliqueKernel s (x :: l)

@[simp] theorem cliqueKernel_zero (H : RGraph W r) (l : List W) :
    H.cliqueKernel 0 l = if l.Nodup ∧ l.toFinset ∈ H.edges then 0 else 1 := rfl

theorem cliqueKernel_zero_eq_zero_iff (H : RGraph W r) (l : List W) :
    H.cliqueKernel 0 l = 0 ↔ l.Nodup ∧ l.toFinset ∈ H.edges := by
  classical
  simp [cliqueKernel]

theorem cliqueKernel_zero_eq_one_of_ne_zero (H : RGraph W r) (l : List W)
    (h : H.cliqueKernel 0 l ≠ 0) : H.cliqueKernel 0 l = 1 := by
  classical
  simp only [cliqueKernel_zero] at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- The tower identity in the form used by the clique potential. -/
@[simp] theorem cliqueKernel_succ (H : RGraph W r) (s : ℕ) (l : List W) :
    H.cliqueKernel (s + 1) l = 𝔼 x : W, H.cliqueKernel s (x :: l) := rfl

theorem cliqueKernel_nonneg (H : RGraph W r) (s : ℕ) (l : List W) :
    0 ≤ H.cliqueKernel s l := by
  classical
  induction s generalizing l with
  | zero => simp only [cliqueKernel_zero]; split_ifs <;> norm_num
  | succ s ih =>
      exact Finset.expect_nonneg (fun x _ => ih (x :: l))

theorem cliqueKernel_le_one [Nonempty W] (H : RGraph W r) (s : ℕ) (l : List W) :
    H.cliqueKernel s l ≤ 1 := by
  classical
  induction s generalizing l with
  | zero => simp only [cliqueKernel_zero]; split_ifs <;> norm_num
  | succ s ih =>
      exact Finset.expect_le Finset.univ_nonempty (fun x _ => ih (x :: l))

/-- Reordering the specified host vertices does not change their failure kernel. -/
theorem cliqueKernel_perm (H : RGraph W r) (s : ℕ) {l l' : List W}
    (h : l.Perm l') : H.cliqueKernel s l = H.cliqueKernel s l' := by
  classical
  induction s generalizing l l' with
  | zero =>
      simp only [cliqueKernel_zero, h.nodup_iff, List.toFinset_eq_of_perm _ _ h]
  | succ s ih =>
      apply Finset.expect_congr rfl
      intro x _
      exact ih (h.cons x)

/-- The paper's sum `S_j`, over `j`-subsets of the assigned domain. -/
noncomputable def cliqueSum (H : RGraph W r) (A : Finset V) (φ : V → W) (j : ℕ) : ℝ :=
  ∑ I ∈ A.powersetCard j, H.cliqueKernel (r - j) (I.toList.map φ)

omit [DecidableEq V] in
theorem cliqueSum_nonneg (H : RGraph W r) (A : Finset V) (φ : V → W) (j : ℕ) :
    0 ≤ H.cliqueSum A φ j := by
  exact Finset.sum_nonneg (fun I _ => H.cliqueKernel_nonneg _ _)

omit [DecidableEq V] in
@[simp] theorem cliqueSum_zero (H : RGraph W r) (A : Finset V) (φ : V → W) :
    H.cliqueSum A φ 0 = H.cliqueKernel r [] := by
  simp [cliqueSum]

omit [DecidableEq V] in
theorem cliqueSum_empty_of_ne_zero (H : RGraph W r) (φ : V → W) {j : ℕ}
    (hj : j ≠ 0) : H.cliqueSum ∅ φ j = 0 := by
  classical
  have hempty : (∅ : Finset V).powersetCard j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro I hI
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hI
    have hI0 : I = ∅ := Finset.subset_empty.mp hsub
    subst I
    exact hj (by simpa using hcard.symm)
  simp [cliqueSum, hempty]

omit [DecidableEq W] [Fintype W] in
theorem map_toList_update_of_not_mem (I : Finset V) (φ : V → W)
    {v : V} (hv : v ∉ I) (x : W) :
    I.toList.map (Function.update φ v x) = I.toList.map φ := by
  apply List.map_congr_left
  intro w hw
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hv (Finset.mem_toList.mp hw)
  exact Function.update_of_ne hwv x φ

/-- The subsets containing the newly inserted vertex give exactly the new
terms in `S_{j+1}`.  The identity also holds for an illegal choice of `x`. -/
theorem cliqueSum_insert (H : RGraph W r) (A : Finset V) (φ : V → W)
    {v : V} (hv : v ∉ A) (x : W) (j : ℕ) :
    H.cliqueSum (insert v A) (Function.update φ v x) (j + 1) =
      H.cliqueSum A φ (j + 1) +
      ∑ I ∈ A.powersetCard j, H.cliqueKernel (r - (j + 1)) (x :: I.toList.map φ) := by
  classical
  have hvI {k : ℕ} {I : Finset V} (hI : I ∈ A.powersetCard k) : v ∉ I :=
    fun h => hv ((Finset.mem_powersetCard.mp hI).1 h)
  have hdisj : Disjoint (A.powersetCard (j + 1))
      ((A.powersetCard j).image (insert v)) := by
    apply Finset.disjoint_left.mpr
    intro I hI hI'
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI'
    exact hvI hI (Finset.mem_insert_self v J)
  have hinj : Set.InjOn (insert v) (A.powersetCard j : Set (Finset V)) := by
    intro I hI J hJ hIJ
    have h := congrArg (fun K : Finset V => K.erase v) hIJ
    simpa [hvI hI, hvI hJ] using h
  unfold cliqueSum
  rw [Finset.powersetCard_succ_insert hv j, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  congr 1
  · apply Finset.sum_congr rfl
    intro I hI
    rw [map_toList_update_of_not_mem I φ (hvI hI) x]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp := (Finset.toList_insert (hvI hI)).map (Function.update φ v x)
    have hp' : ((insert v I).toList.map (Function.update φ v x)).Perm
        (x :: I.toList.map φ) := by
      simpa only [List.map_cons, Function.update_self,
        map_toList_update_of_not_mem I φ (hvI hI) x] using hp
    exact H.cliqueKernel_perm _ hp'

theorem cliqueSum_increment_nonneg (H : RGraph W r) (A : Finset V) (φ : V → W)
    {v : V} (hv : v ∉ A) (x : W) (j : ℕ) :
    0 ≤ H.cliqueSum (insert v A) (Function.update φ v x) j - H.cliqueSum A φ j := by
  cases j with
  | zero => simp
  | succ j =>
      rw [cliqueSum_insert H A φ hv x j, add_sub_cancel_left]
      exact Finset.sum_nonneg (fun I _ => H.cliqueKernel_nonneg _ _)

/-- Averaging the increase in `S_{j+1}` yields `S_j`, as in Claim 2.1(ii). -/
theorem cliqueSum_expected_increment (H : RGraph W r) (A : Finset V) (φ : V → W)
    {v : V} (hv : v ∉ A) (j : ℕ) (hj : j < r) :
    (𝔼 x : W, (H.cliqueSum (insert v A) (Function.update φ v x) (j + 1) -
      H.cliqueSum A φ (j + 1))) = H.cliqueSum A φ j := by
  classical
  simp only [cliqueSum_insert H A φ hv, add_sub_cancel_left]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  have hk : r - j = (r - (j + 1)) + 1 := by omega
  rw [hk, cliqueKernel_succ]

/-- The weighted clique potential `Xi`. -/
noncomputable def cliquePotential (H : RGraph W r) (T : ℝ)
    (A : Finset V) (φ : V → W) : ℝ :=
  ∑ j ∈ Finset.range r, T ^ (r - 1 - j) * H.cliqueSum A φ j

omit [DecidableEq V] in
/-- The initial clique potential has the value used in the manuscript. -/
theorem cliquePotential_empty (H : RGraph W r) (hr : 0 < r) (T : ℝ) (φ : V → W) :
    H.cliquePotential T ∅ φ = T ^ (r - 1) * H.cliqueKernel r [] := by
  classical
  unfold cliquePotential
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [H.cliqueSum_empty_of_ne_zero φ hj0, mul_zero]
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr hr))

omit [DecidableEq V] in
theorem cliquePotential_nonneg (H : RGraph W r) {T : ℝ} (hT : 0 ≤ T)
    (A : Finset V) (φ : V → W) : 0 ≤ H.cliquePotential T A φ := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (pow_nonneg hT _) (H.cliqueSum_nonneg A φ j)

theorem cliquePotential_increment_nonneg (H : RGraph W r) {T : ℝ} (hT : 0 ≤ T)
    (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) (x : W) :
    0 ≤ H.cliquePotential T (insert v A) (Function.update φ v x) -
      H.cliquePotential T A φ := by
  unfold cliquePotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro j hj
  rw [← mul_sub]
  exact mul_nonneg (pow_nonneg hT _) (H.cliqueSum_increment_nonneg A φ hv x j)

/-- The finite weighted-sum identity behind the clique-potential estimate. -/
theorem weighted_clique_shift (S : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    T * (∑ j ∈ Finset.range k, T ^ (k - (j + 1)) * S j) =
      (∑ j ∈ Finset.range (k + 1), T ^ (k - j) * S j) - S k := by
  have hsum : T * (∑ j ∈ Finset.range k, T ^ (k - (j + 1)) * S j) =
      ∑ j ∈ Finset.range k, T ^ (k - j) * S j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    have hk : k - j = (k - (j + 1)) + 1 := by omega
    rw [hk, pow_succ]
    ring
  rw [hsum, Finset.sum_range_succ]
  simp

/-- Multiplying the mean increment by `T` removes exactly the last summand
from the current clique potential. -/
theorem cliquePotential_expected_increment_mul (H : RGraph W r) (hr : 0 < r)
    (T : ℝ) (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) :
    T * (𝔼 x : W,
      (H.cliquePotential T (insert v A) (Function.update φ v x) -
      H.cliquePotential T A φ)) =
      H.cliquePotential T A φ - H.cliqueSum A φ (r - 1) := by
  classical
  cases r with
  | zero => omega
  | succ k =>
      have he : (𝔼 x : W,
          (H.cliquePotential T (insert v A) (Function.update φ v x) -
          H.cliquePotential T A φ)) =
          ∑ j ∈ Finset.range k, T ^ (k - (j + 1)) * H.cliqueSum A φ j := by
        unfold cliquePotential
        simp only [Nat.succ_sub_one]
        simp only [← Finset.sum_sub_distrib, ← mul_sub]
        rw [Finset.expect_sum_comm]
        simp_rw [← Finset.mul_expect]
        rw [Finset.sum_range_succ']
        simp only [cliqueSum_zero, sub_self, Finset.expect_const_zero, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjr : j < k + 1 := by have h := Finset.mem_range.mp hj; omega
        rw [H.cliqueSum_expected_increment A φ hv j hjr]
      rw [he]
      simpa [cliquePotential] using weighted_clique_shift (H.cliqueSum A φ) T k

/-- The exact mean increment from Claim 2.1(ii). -/
theorem cliquePotential_expected_increment (H : RGraph W r) (hr : 0 < r)
    {T : ℝ} (hT : 0 < T) (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) :
    (𝔼 x : W, (H.cliquePotential T (insert v A) (Function.update φ v x) -
      H.cliquePotential T A φ)) =
      (H.cliquePotential T A φ - H.cliqueSum A φ (r - 1)) / T := by
  apply (eq_div_iff (ne_of_gt hT)).mpr
  simpa [mul_comm] using H.cliquePotential_expected_increment_mul hr T A φ hv

/-- The averaged clique-potential increase is at most `Xi/T`. -/
theorem cliquePotential_expected_increment_le (H : RGraph W r) (hr : 0 < r)
    {T : ℝ} (hT : 0 < T) (A : Finset V) (φ : V → W) {v : V} (hv : v ∉ A) :
    (𝔼 x : W, (H.cliquePotential T (insert v A) (Function.update φ v x) -
      H.cliquePotential T A φ)) ≤ H.cliquePotential T A φ / T := by
  rw [H.cliquePotential_expected_increment hr hT A φ hv]
  apply div_le_div_of_nonneg_right _ hT.le
  have h := H.cliqueSum_nonneg A φ (r - 1)
  linarith


end RGraph

end ImprovedSidorenko
