module

public import ImprovedSidorenko.Extremal
public import ImprovedSidorenko.Normalization

@[expose] public section

/-!
# The manuscript's theorem for the classical Turán density

The extremal hosts and their convergence are proved in Extremal.lean.
No convergence hypothesis is supplied by the user of the main theorem.
-/

open Filter Topology

namespace ImprovedSidorenko

noncomputable section

/-- Theorem 1.1 for the formally defined, binomial-normalized Turán density. -/
theorem main_turan_density {r k : ℕ} (hr : 3 ≤ r)
    (F : RGraph (Fin k) r) (hm : 1 ≤ F.edges.card) :
    turanDensity F ≤ 1 - paperGap r F.edges.card := by
  classical
  let H : ∀ n : ℕ, RGraph (Fin n) r :=
    fun n => Classical.choose (F.exists_extremal hm n)
  have hfree : ∀ n, ¬ ∃ f, F.IsEmbedding (H n) f :=
    fun n => (Classical.choose_spec (F.exists_extremal hm n)).1
  have hcard : ∀ n, (H n).edges.card = extremalNumber F n :=
    fun n => (Classical.choose_spec (F.exists_extremal hm n)).2
  have hlimit : Tendsto (fun n => binomialDensity (H n)) atTop (𝓝 (turanDensity F)) := by
    have heq : (fun n => binomialDensity (H n)) = extremalDensity F := by
      funext n
      simp only [binomialDensity, hcard, extremalDensity]
    rw [heq]
    exact extremalDensity_tendsto F hm
  exact main_binomial_limit_bound hr F hm H hfree hlimit

end
end ImprovedSidorenko
