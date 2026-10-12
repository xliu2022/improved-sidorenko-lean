module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# The algebraic descent argument

This file proves the numerical core of Claim 2.2 and the finite-averaging
selection of an improving legal choice.  The expected-update inequality is an
explicit input. Embedding.lean proves that inequality for the actual
hypergraph potentials and uses this descent argument in the finite embedding
proof.
-/

namespace ImprovedSidorenko

noncomputable section

open scoped BigOperators

def combinedPotential (r M Φ Ξ : ℝ) : ℝ := Φ + r ^ 2 * M * Ξ

/-- The maintained budget bounds the clique potential. -/
theorem clique_potential_le {r M Φ Ξ : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hΦ : 0 ≤ Φ)
    (hbudget : combinedPotential r M Φ Ξ ≤ M) : Ξ ≤ 1 / r ^ 2 := by
  unfold combinedPotential at hbudget
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  have h : (Ξ * r ^ 2) * M ≤ 1 * M := by nlinarith only [hbudget, hΦ]
  exact (mul_le_mul_iff_left₀ hM).mp h

/-- The choice of `β` implies the positive decrement coefficient in Claim 2.2. -/
theorem descent_coefficient_pos {r M T β : ℝ}
    (hr : 0 < r) (hT : 0 < T)
    (hβ : β < 1 / r - 4 * M / T) :
    0 < (1 - r * β) * T - 4 * r * M := by
  have hratio : 4 * M / T < 1 / r - β := by linarith
  have hnum := (div_lt_iff₀ hT).mp hratio
  have hmul := mul_lt_mul_of_pos_left hnum hr
  have hid : r * ((1 / r - β) * T) = (1 - r * β) * T := by
    field_simp
  rw [hid] at hmul
  nlinarith only [hmul]

theorem beta_lt_one {r M T β : ℝ}
    (hr : 1 < r) (hM : 0 < M) (hT : 0 < T)
    (hβ : β < 1 / r - 4 * M / T) : β < 1 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r < 1 := (div_lt_one hr0).mpr hr
  have hnonneg : 0 ≤ 4 * M / T := by positivity
  linarith

/-- Algebraic core of the strict descent estimate.  `a` may be the average
updated potential over legal choices.  The assumption `haverage` is the exact
conditional-average estimate from the paper, before using `μ ≤ (r-1)ℓ`.
-/
theorem one_step_strict_descent {r M T β ℓ μ Ξ Ψ a : ℝ}
    (hr : 1 < r) (hM : 0 < M) (hT : 0 < T)
    (hβ0 : 0 ≤ β) (hβ : β < 1 / r - 4 * M / T)
    (hload : 1 / (4 * r) ≤ ℓ) (hμ : μ ≤ (r - 1) * ℓ)
    (hΞ : r ^ 2 * M * Ξ ≤ M)
    (haverage : a ≤ Ψ - ℓ +
      (β * T * μ + r ^ 2 * M * Ξ) / (T * (1 - β))) :
    a < Ψ := by
  have hr0 : 0 < r := by linarith
  have hβ1 : β < 1 := beta_lt_one hr hM hT hβ
  have hden : 0 < T * (1 - β) := mul_pos hT (by linarith)
  have hℓ : 0 < ℓ := lt_of_lt_of_le (by positivity) hload
  have hload' : 1 ≤ ℓ * (4 * r) :=
    (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hload
  have hMload : M ≤ 4 * r * M * ℓ := by
    have h := mul_le_mul_of_nonneg_left hload' hM.le
    nlinarith only [h]
  have hμweighted : β * T * μ ≤ β * T * ((r - 1) * ℓ) :=
    mul_le_mul_of_nonneg_left hμ (mul_nonneg hβ0 hT.le)
  have hgap := descent_coefficient_pos hr0 hT hβ
  have hcoefficient : β * (r - 1) * T + 4 * r * M < T * (1 - β) := by
    nlinarith only [hgap]
  have hnum : β * T * μ + r ^ 2 * M * Ξ < ℓ * (T * (1 - β)) := by
    calc
      β * T * μ + r ^ 2 * M * Ξ
          ≤ β * T * ((r - 1) * ℓ) + 4 * r * M * ℓ :=
            add_le_add hμweighted (hΞ.trans hMload)
      _ = (β * (r - 1) * T + 4 * r * M) * ℓ := by ring
      _ < (T * (1 - β)) * ℓ := mul_lt_mul_of_pos_right hcoefficient hℓ
      _ = ℓ * (T * (1 - β)) := by ring
  have hratio := (div_lt_iff₀ hden).mpr hnum
  linarith

/-- The two usual forms of the conditional expected-update bound coincide. -/
theorem update_bound_rearrange {M T β ℓ μ Ξ Ψ r : ℝ}
    (hT : T ≠ 0) (hβ : 1 - β ≠ 0) :
    Ψ - ℓ - μ + μ / (1 - β) + r ^ 2 * M * Ξ / (T * (1 - β)) =
      Ψ - ℓ + (β * T * μ + r ^ 2 * M * Ξ) / (T * (1 - β)) := by
  field_simp
  ring

/-- Descent with the unrearranged conditional expectation estimate as input. -/
theorem one_step_strict_descent_of_raw_bound {r M T β ℓ μ Ξ Ψ a : ℝ}
    (hr : 1 < r) (hM : 0 < M) (hT : 0 < T)
    (hβ0 : 0 ≤ β) (hβ : β < 1 / r - 4 * M / T)
    (hload : 1 / (4 * r) ≤ ℓ) (hμ : μ ≤ (r - 1) * ℓ)
    (hΞ : r ^ 2 * M * Ξ ≤ M)
    (haverage : a ≤ Ψ - ℓ - μ + μ / (1 - β) +
      r ^ 2 * M * Ξ / (T * (1 - β))) : a < Ψ := by
  have hβ1 := beta_lt_one hr hM hT hβ
  rw [update_bound_rearrange (ne_of_gt hT) (ne_of_gt (sub_pos.mpr hβ1))] at haverage
  exact one_step_strict_descent hr hM hT hβ0 hβ hload hμ hΞ haverage

/-- A finite nonempty family whose average is below a threshold has a member
below that threshold. -/
theorem exists_lt_of_average_lt {α : Type*} (A : Finset α) (hA : A.Nonempty)
    (f : α → ℝ) (c : ℝ)
    (haverage : (∑ x ∈ A, f x) / (A.card : ℝ) < c) :
    ∃ x ∈ A, f x < c := by
  classical
  by_contra h
  push Not at h
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hsum : (A.card : ℝ) * c ≤ ∑ x ∈ A, f x := by
    calc
      (A.card : ℝ) * c = ∑ x ∈ A, c := by simp [nsmul_eq_mul]
      _ ≤ ∑ x ∈ A, f x := Finset.sum_le_sum h
  have hstrict := (div_lt_iff₀ hcard).mp haverage
  nlinarith only [hsum, hstrict]

/-- Claim 2.2's finite-choice conclusion, conditional on the stated averaged
update bound.  `A` is intended to be the set of legal choices and `f x` the
potential after assigning to `x`.
-/
theorem exists_strictly_improving_choice {α : Type*}
    (A : Finset α) (hA : A.Nonempty) (f : α → ℝ)
    {r M T β ℓ μ Ξ Ψ : ℝ}
    (hr : 1 < r) (hM : 0 < M) (hT : 0 < T)
    (hβ0 : 0 ≤ β) (hβ : β < 1 / r - 4 * M / T)
    (hload : 1 / (4 * r) ≤ ℓ) (hμ : μ ≤ (r - 1) * ℓ)
    (hΞ : r ^ 2 * M * Ξ ≤ M)
    (haverage : (∑ x ∈ A, f x) / (A.card : ℝ) ≤ Ψ - ℓ - μ +
      μ / (1 - β) + r ^ 2 * M * Ξ / (T * (1 - β))) :
    ∃ x ∈ A, f x < Ψ := by
  apply exists_lt_of_average_lt A hA f Ψ
  exact one_step_strict_descent_of_raw_bound hr hM hT hβ0 hβ hload hμ hΞ haverage

end

end ImprovedSidorenko
