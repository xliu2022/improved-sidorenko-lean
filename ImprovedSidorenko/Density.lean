module

public import ImprovedSidorenko.Basic
public import ImprovedSidorenko.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# Target statements and the final limiting argument

`MainDensityStatement` and `MainEmbeddingStatement` specify the manuscript's
targets. They are proved, without extra hypotheses, by `main_density` and
`main_embedding` in `Main.lean`. This module provides their precise definitions,
the explicit real-power constant, and general order/limit lemmas.
-/

namespace ImprovedSidorenko

noncomputable section

/-- The positive constant displayed in Theorem 1.1. -/
def paperConstant (r : ℕ) : ℝ :=
  (1 / (4 * (r : ℝ) ^ 2)) *
    Real.rpow (4 / (r : ℝ)) (1 / (r : ℝ)) *
    Real.rpow (1 - 1 / (r : ℝ)) (2 - 2 / (r : ℝ))

/-- The proved gap from density one for an `m`-edge forbidden `r`-graph. -/
def paperGap (r m : ℕ) : ℝ :=
  paperConstant r / Real.rpow (m : ℝ) (((r : ℝ) - 1) / (r : ℝ))

theorem paperConstant_pos {r : ℕ} (hr : 2 ≤ r) : 0 < paperConstant r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hbase : 0 < 1 - 1 / (r : ℝ) := sub_pos.mpr ((div_lt_one hr0).mpr hr1)
  unfold paperConstant
  exact mul_pos (mul_pos (by positivity)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos hbase _)

theorem paperGap_pos {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) : 0 < paperGap r m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact div_pos (paperConstant_pos hr) (Real.rpow_pos_of_pos hm0 _)

/-- Ordered-tuple normalization of the host edge count. -/
def hostDeficit {r n : ℕ} (H : RGraph (Fin n) r) : ℝ :=
  1 - (r.factorial : ℝ) * (H.edges.card : ℝ) / (n : ℝ) ^ r

/-- The finite embedding assertion made inside the proof of Theorem 1.1,
proved by `main_embedding` in `Main.lean`. -/
def MainEmbeddingStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, ∀ F : RGraph (Fin k) r,
    1 ≤ F.edges.card → ∀ q : ℝ, 0 < q → q < paperGap r F.edges.card →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : RGraph (Fin n) r,
        hostDeficit H ≤ q → ∃ f : Fin k → Fin n, F.IsEmbedding H f

/-- A definition of an asymptotic upper bound, not requiring a pre-existing
formalization of the hypergraph Turán-density limit. -/
def TuranUpperBound {r k : ℕ} (F : RGraph (Fin k) r) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ H : RGraph (Fin n) r, (¬ ∃ f : Fin k → Fin n, F.IsEmbedding H f) →
      (r.factorial : ℝ) * (H.edges.card : ℝ) / (n : ℝ) ^ r ≤ b + ε

/-- Theorem 1.1 as an exact asymptotic-upper-bound target. -/
def MainDensityStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, ∀ F : RGraph (Fin k) r,
    1 ≤ F.edges.card → TuranUpperBound F (1 - paperGap r F.edges.card)

/-- The finite embedding assertion implies the asymptotic upper bound.
`Main.lean` applies this lemma to the proved `main_embedding` theorem. -/
theorem main_density_of_main_embedding (hembed : MainEmbeddingStatement) :
    MainDensityStatement := by
  intro r hr k F hm ε hε
  have hc := paperGap_pos (by omega : 2 ≤ r) hm
  have hmax : max 0 (paperGap r F.edges.card - ε) < paperGap r F.edges.card :=
    max_lt hc (by linarith)
  obtain ⟨q, hq, hqc⟩ := exists_between hmax
  have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqε : paperGap r F.edges.card - ε < q := lt_of_le_of_lt (le_max_right _ _) hq
  obtain ⟨N, hN⟩ := hembed r hr k F hm q hq0 hqc
  refine ⟨N, ?_⟩
  intro n hn H hfree
  have hdef : q < hostDeficit H := by
    by_contra h
    exact hfree (hN n hn H (le_of_not_gt h))
  unfold hostDeficit at hdef
  linarith

open Filter in
/-- The final limit argument in the manuscript, isolated from the finite
embedding and extremal-counting obligations. -/
theorem density_bound_of_eventual_deficit (u : ℕ → ℝ) (π c : ℝ)
    (hc : 0 < c) (hlimit : Tendsto u atTop (nhds π))
    (hembed : ∀ q : ℝ, 0 < q → q < c → ∀ᶠ n in atTop, u n < 1 - q) :
    π ≤ 1 - c := by
  have hbound : ∀ q : ℝ, 0 < q → q < c → π ≤ 1 - q := by
    intro q hq hqc
    exact le_of_tendsto hlimit ((hembed q hq hqc).mono (fun _ h => h.le))
  by_contra h
  have hπ : 1 - c < π := lt_of_not_ge h
  have hmax : max 0 (1 - π) < c := max_lt hc (by linarith)
  obtain ⟨q, hq, hqc⟩ := exists_between hmax
  have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqπ : 1 - π < q := lt_of_le_of_lt (le_max_right _ _) hq
  have hb := hbound q hq0 hqc
  linarith

end
end ImprovedSidorenko
