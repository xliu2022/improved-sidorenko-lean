module

public import ImprovedSidorenko.Main
public import Mathlib.Analysis.SpecialFunctions.Choose

@[expose] public section

/-!
# Passing to the usual binomial normalization

The main finite theorem uses `r! |E(H)| / n^r`.  This file proves the
normalization factor tends to one, uniformly transfers the asymptotic bound
to `|E(H)| / choose n r`, and bounds every limit of a sequence of `F`-free
hosts in that usual normalization.  In particular the limit theorem applies
to any choice of extremal hosts, if their normalized counts converge.

No asymptotic normalization identity is assumed. The existence of the
classical Turán-density limit is proved in Extremal.lean, and TuranDensity.lean
applies this bound to the formally constructed extremal hosts.
-/

open Filter Topology

namespace ImprovedSidorenko

noncomputable section

/-- The fraction of ordered `r`-samples with distinct coordinates. -/
def normalizationFactor (r n : ℕ) : ℝ :=
  (r.factorial : ℝ) * (n.choose r : ℝ) / (n : ℝ) ^ r

/-- The conversion factor for the two density normalizations tends to one. -/
theorem normalizationFactor_tendsto (r : ℕ) :
    Tendsto (normalizationFactor r) atTop (𝓝 1) := by
  have hz : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ r / (r.factorial : ℝ) ≠ 0 := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp (isEquivalent_choose r)
  convert h using 1
  ext n
  simp only [normalizationFactor, Pi.div_apply, div_div_eq_mul_div, mul_comm]

/-- The usual host edge density, with denominator `choose n r`. -/
def binomialDensity {r n : ℕ} (H : RGraph (Fin n) r) : ℝ :=
  (H.edges.card : ℝ) / (n.choose r : ℝ)

theorem binomialDensity_nonneg {r n : ℕ} (H : RGraph (Fin n) r) :
    0 ≤ binomialDensity H := by unfold binomialDensity; positivity

theorem binomialDensity_le_one {r n : ℕ} (H : RGraph (Fin n) r) (hn : r ≤ n) :
    binomialDensity H ≤ 1 := by
  have hc : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply (div_le_iff₀ hc).mpr
  simpa only [one_mul] using (Nat.cast_le.mpr H.edge_card_le_choose :
    (H.edges.card : ℝ) ≤ n.choose r)

/-- An exact finite relation between the two density normalizations. -/
theorem ordered_density_eq_factor_mul_binomial {r n : ℕ}
    (H : RGraph (Fin n) r) (hn : r ≤ n) :
    (r.factorial : ℝ) * H.edges.card / (n : ℝ) ^ r =
      normalizationFactor r n * binomialDensity H := by
  have hc : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  unfold normalizationFactor binomialDensity
  symm
  calc
    (r.factorial : ℝ) * n.choose r / (n : ℝ) ^ r *
        ((H.edges.card : ℝ) / n.choose r) =
        ((r.factorial : ℝ) * H.edges.card) * n.choose r /
          ((n : ℝ) ^ r * n.choose r) := by
            rw [div_mul_div_comm]
            congr 1
            ring
    _ = (r.factorial : ℝ) * H.edges.card / (n : ℝ) ^ r :=
      mul_div_mul_right _ _ hc

/-- An asymptotic Turán upper bound in the usual binomial normalization. -/
def BinomialTuranUpperBound {r k : ℕ} (F : RGraph (Fin k) r) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ H : RGraph (Fin n) r, (¬ ∃ f : Fin k → Fin n, F.IsEmbedding H f) →
      binomialDensity H ≤ b + ε

/-- The ordered-tuple asymptotic upper bound implies the usual one.
The estimate is uniform over every host on the given number of vertices. -/
theorem binomial_turanUpperBound_of_ordered {r k : ℕ} {F : RGraph (Fin k) r}
    {b : ℝ} (hupper : TuranUpperBound F b) : BinomialTuranUpperBound F b := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hupper (ε / 2) (by linarith)
  have hfactor : ∀ᶠ n in atTop, 1 - ε / 2 < normalizationFactor r n :=
    (normalizationFactor_tendsto r).eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hfactor
  refine ⟨max r (max N₁ N₂), ?_⟩
  intro n hn H hfree
  have hrn : r ≤ n := (le_max_left _ _).trans hn
  have h₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_right _ _).trans hn)
  have h₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_right _ _).trans hn)
  have hu0 := binomialDensity_nonneg H
  have hu1 := binomialDensity_le_one H hrn
  have hprod := mul_le_mul_of_nonneg_right (hN₂ n h₂).le hu0
  have hεprod : ε / 2 * binomialDensity H ≤ ε / 2 := by nlinarith
  have ho := hN₁ n h₁ H hfree
  rw [ordered_density_eq_factor_mul_binomial H hrn] at ho
  nlinarith

/-- Theorem 1.1 as an asymptotic bound with denominator `choose n r`. -/
theorem main_binomial_density :
    ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, ∀ F : RGraph (Fin k) r,
      1 ≤ F.edges.card → BinomialTuranUpperBound F (1 - paperGap r F.edges.card) := by
  intro r hr k F hm
  exact binomial_turanUpperBound_of_ordered (main_density r hr k F hm)

/-- Any convergent sequence of `F`-free host densities has limit at most the
uniform asymptotic upper bound.  Extremal hosts are one possible such sequence. -/
theorem binomial_limit_le_of_upperBound {r k : ℕ} {F : RGraph (Fin k) r}
    {b : ℝ} (hupper : BinomialTuranUpperBound F b)
    (H : ∀ n : ℕ, RGraph (Fin n) r)
    (hfree : ∀ n, ¬ ∃ f : Fin k → Fin n, F.IsEmbedding (H n) f)
    {π : ℝ} (hlimit : Tendsto (fun n => binomialDensity (H n)) atTop (𝓝 π)) :
    π ≤ b := by
  by_contra h
  have hb : b < π := lt_of_not_ge h
  obtain ⟨N, hN⟩ := hupper ((π - b) / 2) (by linarith)
  have hev : ∀ᶠ n in atTop, binomialDensity (H n) ≤ b + (π - b) / 2 :=
    eventually_atTop.mpr ⟨N, fun n hn => hN n hn (H n) (hfree n)⟩
  have hlim := le_of_tendsto hlimit hev
  linarith

/-- The paper's numerical bound for any limit of usual densities of `F`-free
hosts; in particular it applies to the classical extremal-density limit. -/
theorem main_binomial_limit_bound {r k : ℕ} (hr : 3 ≤ r)
    (F : RGraph (Fin k) r) (hm : 1 ≤ F.edges.card)
    (H : ∀ n : ℕ, RGraph (Fin n) r)
    (hfree : ∀ n, ¬ ∃ f : Fin k → Fin n, F.IsEmbedding (H n) f)
    {π : ℝ} (hlimit : Tendsto (fun n => binomialDensity (H n)) atTop (𝓝 π)) :
    π ≤ 1 - paperGap r F.edges.card :=
  binomial_limit_le_of_upperBound (main_binomial_density r hr k F hm) H hfree hlimit

end
end ImprovedSidorenko
