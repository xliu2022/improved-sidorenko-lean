module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# Improved Sidorenko bound for hypergraph Turán densities

This independent statement module uses only Mathlib and Lean core. It states
the finite embedding assertion, the existence of the classical Turán-density
limit, and Theorem 1.1 of the manuscript by Shuyan Chen, Xinmin Hou and Xizhi Liu.
The corresponding Solution contains proofs of the same declarations.

The extremal number below is a maximum over actual F-free hosts. The density
is defined by an infimum, and `Registry.limit_exists` proves that it is the
ordinary limit of the binomial-normalized extremal numbers. Thus the main
theorem has no convergence or extremal-existence hypothesis.
-/

open Filter Topology

namespace ImprovedSidorenko

universe u v

/-- A simple r-uniform hypergraph with a finite edge set. The main statements
use finite vertex types Fin k. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- An embedding is globally injective and preserves every edge. -/
def RGraph.IsEmbedding {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] {r : ℕ}
    (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

noncomputable section

/-- The exact positive constant displayed in Theorem 1.1 for r >= 3. -/
def paperConstant (r : ℕ) : ℝ :=
  (1 / (4 * (r : ℝ) ^ 2)) *
    Real.rpow (4 / (r : ℝ)) (1 / (r : ℝ)) *
    Real.rpow (1 - 1 / (r : ℝ)) (2 - 2 / (r : ℝ))

/-- The claimed gap from density one for an m-edge forbidden hypergraph. -/
def paperGap (r m : ℕ) : ℝ :=
  paperConstant r / Real.rpow (m : ℝ) (((r : ℝ) - 1) / (r : ℝ))

/-- The maximum number of edges of an F-free n-vertex r-graph, with the
convention zero if no such host exists. The search bound counts all r-sets. -/
def extremalNumber {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ H : RGraph (Fin n) r,
    (¬ ∃ f, F.IsEmbedding H f) ∧ H.edges.card = m) (n.choose r)

/-- The binomial-normalized extremal number ex(n,F)/choose(n,r). -/
def extremalDensity {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℝ :=
  (extremalNumber F n : ℝ) / (n.choose r : ℝ)

/-- The infimum of normalized extremal numbers for n >= r. The limit theorem
below identifies this number with the classical Turán density. -/
def turanDensity {r k : ℕ} (F : RGraph (Fin k) r) : ℝ :=
  ⨅ n : ℕ, extremalDensity F (n + r)

namespace Registry

/-- Every sufficiently dense large host contains a globally injective copy
of F, including its isolated vertices. The threshold is uniform over hosts. -/
theorem embedding {r k : ℕ} (hr : 3 ≤ r) (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) {q : ℝ} (hq : 0 < q)
    (hgap : q < paperGap r F.edges.card) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : RGraph (Fin n) r,
      1 - (r.factorial : ℝ) * (H.edges.card : ℝ) / (n : ℝ) ^ r ≤ q →
      ∃ f : Fin k → Fin n, F.IsEmbedding H f := by
  sorry

/-- The Katona--Nemetz--Simonovits limit-existence theorem for a single
finite forbidden hypergraph with at least one edge. -/
theorem limit_exists {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) :
    Tendsto (extremalDensity F) atTop (𝓝 (turanDensity F)) := by
  sorry

/-- Theorem 1.1 of the source manuscript, for the classical Turán density
with its existence proved, using the exact displayed real-power constant. -/
theorem main_theorem {r k : ℕ} (hr : 3 ≤ r)
    (F : RGraph (Fin k) r) (hm : 1 ≤ F.edges.card) :
    turanDensity F ≤ 1 - paperGap r F.edges.card := by
  sorry

end Registry
end
end ImprovedSidorenko
