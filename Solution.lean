module

public import ImprovedSidorenko

@[expose] public section

/-!
# Proofs of the Palomar statements

This module imports the full development, not Challenge. Comparator compares
these declarations with the independently stated Challenge declarations.
-/

open Filter Topology

namespace ImprovedSidorenko.Registry

theorem embedding {r k : ℕ} (hr : 3 ≤ r) (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) {q : ℝ} (hq : 0 < q)
    (hgap : q < paperGap r F.edges.card) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : RGraph (Fin n) r,
      1 - (r.factorial : ℝ) * (H.edges.card : ℝ) / (n : ℝ) ^ r ≤ q →
      ∃ f : Fin k → Fin n, F.IsEmbedding H f :=
  main_embedding r hr k F hm q hq hgap

theorem limit_exists {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) :
    Tendsto (extremalDensity F) atTop (𝓝 (turanDensity F)) :=
  extremalDensity_tendsto F hm

theorem main_theorem {r k : ℕ} (hr : 3 ≤ r)
    (F : RGraph (Fin k) r) (hm : 1 ≤ F.edges.card) :
    turanDensity F ≤ 1 - paperGap r F.edges.card :=
  main_turan_density hr F hm

end ImprovedSidorenko.Registry
