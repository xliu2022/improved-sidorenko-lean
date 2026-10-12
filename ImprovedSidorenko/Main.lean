module

public import ImprovedSidorenko.Embedding
public import ImprovedSidorenko.KernelBridge
public import ImprovedSidorenko.Density
public import ImprovedSidorenko.Constant
public import ImprovedSidorenko.Counting

@[expose] public section

/-!
# The finite embedding theorem and the density bound

This file chooses the numerical parameters, makes the host-size requirement
explicit, and connects the initial potential with the unconditional host
failure kernel. The final theorems connect that kernel to the actual edge count
and use the constant displayed in the manuscript.
-/

namespace ImprovedSidorenko

noncomputable section

/-- The complete embedding argument for the polynomial form of the smallness
condition. The host hypothesis is expressed using its actual failure kernel.
The witness `N` is positive, so all subsequent host averages are over nonempty
types. -/
theorem kernel_embedding_of_polynomial_bound {r k : ℕ}
    (hr : 2 ≤ r) (F : RGraph (Fin k) r) (hm : 1 ≤ F.edges.card)
    {q : ℝ} (hq : 0 < q)
    (hsmall : (F.edges.card : ℝ) ^ (r - 1) * q ^ r < criticalPower r) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ H : RGraph (Fin n) r,
      H.cliqueKernel r [] ≤ q → ∃ f : Fin k → Fin n, F.IsEmbedding H f := by
  classical
  have hrR : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  have hrNat : 0 < r := by omega
  have hmR : (0 : ℝ) < F.edges.card := by
    exact_mod_cast (show 0 < F.edges.card by omega)
  obtain ⟨T, β, hT, _, hupper, hβlower, hβupper⟩ :=
    exists_parameters hr hmR hq hsmall
  have hM : 0 < mass r F.edges.card q := mass_pos hrR hmR hq
  have hδ : 0 < β - 1 / (r : ℝ) ^ 2 := by linarith
  have hβ0 : 0 ≤ β := by
    have hh : (0 : ℝ) < 1 / (r : ℝ) ^ 2 := by positivity
    linarith
  have hbase : 0 < 1 - 1 / (2 * (r : ℝ)) := by
    apply sub_pos.mpr
    apply (div_lt_one (by positivity : (0 : ℝ) < 2 * (r : ℝ))).mpr
    linarith
  have hbasepow : 0 < (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card :=
    pow_pos hbase _
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (1 : ℝ) (max ((k : ℝ) / (β - 1 / (r : ℝ) ^ 2))
      ((k.choose 2 : ℝ) / (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card)))
  refine ⟨N, ?_, ?_⟩
  · have h1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast h1.le
  · intro n hn H hkernel
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hbound := lt_of_lt_of_le hN hNn
    obtain ⟨hnOne, hnRest⟩ := max_lt_iff.mp hbound
    obtain ⟨hnCard, hnCollision⟩ := max_lt_iff.mp hnRest
    have hnR : (0 : ℝ) < n := by linarith
    have hnNat : 0 < n := by exact_mod_cast hnR
    letI : Nonempty (Fin n) := ⟨⟨0, hnNat⟩⟩
    let φ₀ : Fin k → Fin n := fun _ => ⟨0, hnNat⟩
    have hcards : (Fintype.card (Fin k) : ℝ) / Fintype.card (Fin n) ≤
        β - 1 / (r : ℝ) ^ 2 := by
      simp only [Fintype.card_fin]
      apply (div_le_iff₀ hnR).mpr
      have hh := (div_lt_iff₀ hδ).mp hnCard
      nlinarith only [hh]
    have hcollision : ((Fintype.card (Fin k)).choose 2 : ℝ) /
        Fintype.card (Fin n) < (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card := by
      simp only [Fintype.card_fin]
      apply (div_lt_iff₀ hnR).mpr
      have hh := (div_lt_iff₀ hbasepow).mp hnCollision
      nlinarith only [hh]
    have hinit : F.totalPotential H T (mass r F.edges.card q) ∅ φ₀ <
        mass r F.edges.card q := by
      calc
        F.totalPotential H T (mass r F.edges.card q) ∅ φ₀ =
            (r : ℝ) * F.edges.card * H.cliqueKernel r [] +
            (r : ℝ) ^ 2 * mass r F.edges.card q *
              (H.cliqueKernel r [] * T ^ (r - 1)) := by
                unfold RGraph.totalPotential
                rw [F.edgePotential_empty H φ₀, H.cliquePotential_empty hrNat T φ₀]
                ring
        _ < mass r F.edges.card q :=
          initial_potential_lt_mass hr hmR hq hkernel hT hupper
    exact F.embedding_of_initial_potential H hr T (mass r F.edges.card q) β
      hT hM hβ0 hβupper hcards φ₀ hinit hcollision

/-- The finite embedding assertion in the proof of Theorem 1.1, with the
displayed real-power constant and the actual host edge-count deficit. -/
theorem main_embedding : MainEmbeddingStatement := by
  intro r hr k F hm q hq hgap
  have hr2 : 2 ≤ r := by omega
  have hsmall := polynomial_small_of_lt_paperGap hr2 hm hq.le hgap
  obtain ⟨N, hN0, hN⟩ := kernel_embedding_of_polynomial_bound hr2 F hm hq hsmall
  refine ⟨N, ?_⟩
  intro n hn H hdef
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  apply hN n hn H
  rw [H.cliqueKernel_empty_eq_density]
  simpa only [hostDeficit, Fintype.card_fin] using hdef

/-- Theorem 1.1 in asymptotic-upper-bound form. Every finite hypergraph with
`m ≥ 1` edges has density at most `1 - paperConstant r / m^((r-1)/r)`.
The edge normalization is the ordered-tuple convention `r! |E| / n^r`. -/
theorem main_density : MainDensityStatement :=
  main_density_of_main_embedding main_embedding

end
end ImprovedSidorenko
