module

public import ImprovedSidorenko.Density

@[expose] public section

/-!
# The displayed real-power constant and its polynomial form

These equalities connect the constant in the manuscript with the natural-power
smallness condition used in `Parameters.lean`.
-/

namespace ImprovedSidorenko

noncomputable section

theorem paperConstant_pow {r : ℕ} (hr : 2 ≤ r) :
    paperConstant r ^ r = criticalPower r := by
  have hrn : r ≠ 0 := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hb : 0 < 1 - 1 / (r : ℝ) := sub_pos.mpr ((div_lt_one hr0).mpr hr1)
  have hsecond : Real.rpow (4 / (r : ℝ)) (1 / (r : ℝ)) ^ r = 4 / (r : ℝ) := by
    simpa only [Real.rpow_eq_pow, one_div] using
      Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 4 / (r : ℝ)) hrn
  have hexp : (2 - 2 / (r : ℝ)) * (r : ℝ) = ((2 * r - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * r), Nat.cast_mul]
    norm_num
    field_simp
  have hthird : Real.rpow (1 - 1 / (r : ℝ)) (2 - 2 / (r : ℝ)) ^ r =
      (1 - 1 / (r : ℝ)) ^ (2 * r - 2) := by
    calc
      Real.rpow (1 - 1 / (r : ℝ)) (2 - 2 / (r : ℝ)) ^ r
          = Real.rpow (1 - 1 / (r : ℝ)) ((2 - 2 / (r : ℝ)) * (r : ℝ)) :=
            (Real.rpow_mul_natCast hb.le _ r).symm
      _ = (1 - 1 / (r : ℝ)) ^ (2 * r - 2) := by
            rw [hexp]
            exact Real.rpow_natCast _ _
  have hbase : 1 - 1 / (r : ℝ) = ((r : ℝ) - 1) / (r : ℝ) := by
    field_simp
  have h4 : (4 : ℝ) ^ r = 4 ^ (r - 1) * 4 := by
    have hk : r = (r - 1) + 1 := by omega
    nth_rw 1 [hk]
    rw [pow_succ]
  have hrpow : (r : ℝ) ^ (4 * r - 1) =
      ((r : ℝ) ^ 2) ^ r * (r : ℝ) ^ (2 * r - 2) * (r : ℝ) := by
    rw [← pow_mul, ← pow_add, ← pow_succ]
    congr 1
    omega
  unfold paperConstant
  rw [mul_pow, mul_pow, hsecond, hthird, hbase]
  simp only [div_pow, mul_pow, one_pow]
  rw [criticalPower_eq hr, h4, hrpow]
  field_simp

theorem paperGap_pow {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) :
    paperGap r m ^ r = criticalPower r / (m : ℝ) ^ (r - 1) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hexp : (((r : ℝ) - 1) / (r : ℝ)) * (r : ℝ) = ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    field_simp
  have hden : Real.rpow (m : ℝ) (((r : ℝ) - 1) / (r : ℝ)) ^ r =
      (m : ℝ) ^ (r - 1) := by
    calc
      Real.rpow (m : ℝ) (((r : ℝ) - 1) / (r : ℝ)) ^ r
          = Real.rpow (m : ℝ) ((((r : ℝ) - 1) / (r : ℝ)) * (r : ℝ)) :=
            (Real.rpow_mul_natCast hm0.le _ r).symm
      _ = (m : ℝ) ^ (r - 1) := by
            rw [hexp]
            exact Real.rpow_natCast _ _
  unfold paperGap
  rw [div_pow, paperConstant_pow hr, hden]

/-- The paper's gap hypothesis is equivalent to the natural-power condition. -/
theorem lt_paperGap_iff {r m : ℕ} {q : ℝ}
    (hr : 2 ≤ r) (hm : 1 ≤ m) (hq : 0 ≤ q) :
    q < paperGap r m ↔ (m : ℝ) ^ (r - 1) * q ^ r < criticalPower r := by
  have hrn : r ≠ 0 := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hgap0 : 0 ≤ paperGap r m := (paperGap_pos hr hm).le
  rw [← pow_lt_pow_iff_left₀ hq hgap0 hrn, paperGap_pow hr hm,
    lt_div_iff₀ (pow_pos hm0 _)]
  simp [mul_comm]

theorem polynomial_small_of_lt_paperGap {r m : ℕ} {q : ℝ}
    (hr : 2 ≤ r) (hm : 1 ≤ m) (hq : 0 ≤ q) (hgap : q < paperGap r m) :
    (m : ℝ) ^ (r - 1) * q ^ r < criticalPower r :=
  (lt_paperGap_iff hr hm hq).mp hgap

end

end ImprovedSidorenko
