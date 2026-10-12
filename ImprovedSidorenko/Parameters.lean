module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The numerical parameter choice

This file formalizes the algebraic parameter choice in Section 2 of
Chen--Hou--Liu, *Improved Sidorenko bound for hypergraph Turán densities*.
The small-density hypothesis is expressed using natural powers, avoiding a
separate theory of real fractional powers.  `criticalPower r` is the quantity
called `c_r ^ r` in the manuscript; its equivalence with the displayed rational
expression is proved below.

This file proves numerical statements only.  It does not define a hypergraph
or establish the main Turán-density theorem.
-/

namespace ImprovedSidorenko

noncomputable section

/-- The coefficient in the lower endpoint of the `T` window. -/
def lowerCoefficient (r : ℝ) : ℝ := 4 * r ^ 4 / (r - 1) ^ 2

/-- The mass budget `M` from the paper. -/
def mass (r m q : ℝ) : ℝ := r ^ 2 * m * q / (r - 1)

/-- The lower endpoint of the admissible `T` interval. -/
def lowerThreshold (r m q : ℝ) : ℝ := lowerCoefficient r * m * q

/-- The `r`th power of the paper's constant, in factored form. -/
def criticalPower (r : ℕ) : ℝ :=
  1 / ((r : ℝ) ^ 3 * lowerCoefficient r ^ (r - 1))

theorem lowerCoefficient_pos {r : ℝ} (hr : 1 < r) :
    0 < lowerCoefficient r := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  unfold lowerCoefficient
  positivity

theorem mass_pos {r m q : ℝ} (hr : 1 < r) (hm : 0 < m) (hq : 0 < q) :
    0 < mass r m q := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  unfold mass
  positivity

theorem lowerThreshold_pos {r m q : ℝ}
    (hr : 1 < r) (hm : 0 < m) (hq : 0 < q) :
    0 < lowerThreshold r m q := by
  exact mul_pos (mul_pos (lowerCoefficient_pos hr) hm) hq

theorem criticalPower_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < criticalPower r := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  unfold criticalPower
  exact one_div_pos.mpr (mul_pos (by positivity)
    (pow_pos (lowerCoefficient_pos hr') _))

/-- The factored constant is exactly the rational expression `c_r ^ r`
displayed in the manuscript. -/
theorem criticalPower_eq {r : ℕ} (hr : 2 ≤ r) :
    criticalPower r = ((r : ℝ) - 1) ^ (2 * r - 2) /
      (4 ^ (r - 1) * (r : ℝ) ^ (4 * r - 1)) := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hr1ne : (r : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hr')
  have hexp2 : 2 * r - 2 = 2 * (r - 1) := by omega
  have hexp4 : 4 * r - 1 = 4 * (r - 1) + 3 := by omega
  rw [hexp2, hexp4, pow_add, pow_mul, pow_mul]
  unfold criticalPower lowerCoefficient
  rw [div_pow, mul_pow]
  field_simp

/-- A strictly feasible natural-power inequality remains feasible at a slightly
larger point.  This is the only continuity argument needed for choosing `T`. -/
theorem exists_larger_power_bound (a b : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (h : b * a ^ k < 1) :
    ∃ T : ℝ, 0 < T ∧ a < T ∧ b * T ^ k < 1 := by
  have hopen : IsOpen {x : ℝ | b * x ^ k < 1} :=
    isOpen_lt (continuous_const.mul (continuous_id.pow k)) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a h
  refine ⟨a + ε / 2, by linarith, by linarith, ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_of_pos (by linarith : 0 < a + ε / 2 - a)]
  linarith

/-- The small-density condition implies the polynomial form of the `T` window.
The upper condition is equivalent to the upper endpoint in the manuscript for
positive `T` and `q`. -/
theorem exists_T_window {r : ℕ} {m q : ℝ}
    (hr : 2 ≤ r) (hm : 0 < m) (hq : 0 < q)
    (hsmall : m ^ (r - 1) * q ^ r < criticalPower r) :
    ∃ T : ℝ, 0 < T ∧ lowerThreshold r m q < T ∧
      (r : ℝ) ^ 3 * q * T ^ (r - 1) < 1 := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  have hk : r - 1 + 1 = r := by omega
  have hcoeff : 0 < (r : ℝ) ^ 3 * lowerCoefficient r ^ (r - 1) :=
    mul_pos (by positivity) (pow_pos (lowerCoefficient_pos hr') _)
  have hsmall' : ((r : ℝ) ^ 3 * lowerCoefficient r ^ (r - 1)) *
      (m ^ (r - 1) * q ^ r) < 1 := by
    have h := (lt_div_iff₀ hcoeff).mp hsmall
    simpa [mul_comm] using h
  have hendpoint : (r : ℝ) ^ 3 * q *
      lowerThreshold r m q ^ (r - 1) < 1 := by
    calc
      (r : ℝ) ^ 3 * q * lowerThreshold r m q ^ (r - 1)
          = ((r : ℝ) ^ 3 * lowerCoefficient r ^ (r - 1)) *
              (m ^ (r - 1) * (q ^ (r - 1) * q)) := by
                simp only [lowerThreshold, mul_pow]
                ring
      _ = ((r : ℝ) ^ 3 * lowerCoefficient r ^ (r - 1)) *
              (m ^ (r - 1) * q ^ r) := by rw [← pow_succ, hk]
      _ < 1 := hsmall'
  exact exists_larger_power_bound _ _ _
    (lowerThreshold_pos hr' hm hq).le hendpoint

/-- The lower endpoint has the useful alternative expression `4 r² M/(r-1)`. -/
theorem lowerThreshold_eq_mass {r m q : ℝ} (hr : 1 < r) :
    lowerThreshold r m q = 4 * r ^ 2 * mass r m q / (r - 1) := by
  have hr1 : r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  unfold lowerThreshold lowerCoefficient mass
  field_simp

/-- The strict lower bound on `T` leaves a nonempty interval for `β`. -/
theorem beta_interval_nonempty {r m q T : ℝ}
    (hr : 1 < r) (hT : 0 < T) (hwindow : lowerThreshold r m q < T) :
    1 / r ^ 2 < 1 / r - 4 * mass r m q / T := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  rw [lowerThreshold_eq_mass hr] at hwindow
  have hnum := (div_lt_iff₀ (sub_pos.mpr hr)).mp hwindow
  have hratio : 4 * mass r m q / T < (r - 1) / r ^ 2 := by
    apply (div_lt_div_iff₀ hT hr2).mpr
    nlinarith only [hnum]
  have hid : (r - 1) / r ^ 2 = 1 / r - 1 / r ^ 2 := by
    field_simp [ne_of_gt hr0]
  rw [hid] at hratio
  linarith

theorem exists_beta {r m q T : ℝ}
    (hr : 1 < r) (hT : 0 < T) (hwindow : lowerThreshold r m q < T) :
    ∃ β : ℝ, 1 / r ^ 2 < β ∧ β < 1 / r - 4 * mass r m q / T :=
  exists_between (beta_interval_nonempty hr hT hwindow)

/-- The full numerical choice preceding the construction of the host embedding. -/
theorem exists_parameters {r : ℕ} {m q : ℝ}
    (hr : 2 ≤ r) (hm : 0 < m) (hq : 0 < q)
    (hsmall : m ^ (r - 1) * q ^ r < criticalPower r) :
    ∃ T β : ℝ, 0 < T ∧ lowerThreshold r m q < T ∧
      (r : ℝ) ^ 3 * q * T ^ (r - 1) < 1 ∧
      1 / (r : ℝ) ^ 2 < β ∧
      β < 1 / (r : ℝ) - 4 * mass r m q / T := by
  obtain ⟨T, hT, hlow, hupp⟩ := exists_T_window hr hm hq hsmall
  obtain ⟨β, hβlow, hβupp⟩ :=
    exists_beta (show (1 : ℝ) < r by exact_mod_cast (show 1 < r by omega)) hT hlow
  exact ⟨T, β, hT, hlow, hupp, hβlow, hβupp⟩

/-- The initial combined potential is strictly below `M`.
Here `qH` is the host's actual failure density; its interpretation is not assumed
or established by this purely numerical lemma. -/
theorem initial_potential_lt_mass {r : ℕ} {m q qH T : ℝ}
    (hr : 2 ≤ r) (hm : 0 < m) (hq : 0 < q) (hqH : qH ≤ q)
    (hT : 0 < T) (hupp : (r : ℝ) ^ 3 * q * T ^ (r - 1) < 1) :
    (r : ℝ) * m * qH + (r : ℝ) ^ 2 * mass r m q *
      (qH * T ^ (r - 1)) < mass r m q := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hr1ne : (r : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hr')
  have hM : 0 < mass r m q := mass_pos hr' hm hq
  have hfrac : 0 < mass r m q / (r : ℝ) := div_pos hM hr0
  have hxi : (r : ℝ) ^ 2 * mass r m q * (q * T ^ (r - 1)) <
      mass r m q / (r : ℝ) := by
    calc
      (r : ℝ) ^ 2 * mass r m q * (q * T ^ (r - 1))
          = (mass r m q / (r : ℝ)) * ((r : ℝ) ^ 3 * q * T ^ (r - 1)) := by
            field_simp
      _ < (mass r m q / (r : ℝ)) * 1 := mul_lt_mul_of_pos_left hupp hfrac
      _ = mass r m q / (r : ℝ) := by ring
  have hmass : (r : ℝ) * m * q + mass r m q / (r : ℝ) = mass r m q := by
    unfold mass
    field_simp
    ring
  calc
    (r : ℝ) * m * qH + (r : ℝ) ^ 2 * mass r m q * (qH * T ^ (r - 1))
        ≤ (r : ℝ) * m * q + (r : ℝ) ^ 2 * mass r m q * (q * T ^ (r - 1)) := by
          gcongr
    _ < (r : ℝ) * m * q + mass r m q / (r : ℝ) := add_lt_add_right hxi _
    _ = mass r m q := hmass

end

end ImprovedSidorenko
