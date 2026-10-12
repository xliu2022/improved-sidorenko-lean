module

public import ImprovedSidorenko.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# Extremal numbers and the existence of Turán density

The extremal number is the largest edge count of an actual F-free host.
Deleting each host vertex and counting surviving edges proves that the
binomial-normalized extremal numbers are nonincreasing for n >= r.
Their nonnegativity then gives the Katona--Nemetz--Simonovits limit.
-/

open scoped BigOperators
open Filter Topology

namespace ImprovedSidorenko

noncomputable section

/-- The largest edge count of an F-free simple r-graph on Fin n; zero if
there is no such host. The upper search bound counts all possible r-edges. -/
def extremalNumber {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ H : RGraph (Fin n) r,
    (¬ ∃ f, F.IsEmbedding H f) ∧ H.edges.card = m) (n.choose r)

/-- The usual binomial-normalized extremal number. -/
def extremalDensity {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℝ :=
  (extremalNumber F n : ℝ) / (n.choose r : ℝ)

/-- Turán density, defined as the infimum of the normalized extremal numbers
for n >= r. The limit theorem below proves that this is their ordinary limit. -/
def turanDensity {r k : ℕ} (F : RGraph (Fin k) r) : ℝ :=
  ⨅ n : ℕ, extremalDensity F (n + r)

namespace RGraph

/-- The empty r-graph on a finite vertex set. -/
def empty (V : Type*) [DecidableEq V] (r : ℕ) : RGraph V r where
  edges := ∅
  uniform := by simp

theorem empty_is_free {r k n : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) : ¬ ∃ f, F.IsEmbedding (empty (Fin n) r) f := by
  classical
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < F.edges.card by omega)
  rintro ⟨f, hf⟩
  simpa [empty] using hf.2 e he

theorem edge_card_le_extremalNumber {r k n : ℕ} (F : RGraph (Fin k) r)
    (H : RGraph (Fin n) r) (hfree : ¬ ∃ f, F.IsEmbedding H f) :
    H.edges.card ≤ extremalNumber F n := by
  classical
  exact Nat.le_findGreatest H.edge_card_le_choose ⟨H, hfree, rfl⟩

theorem exists_extremal {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) (n : ℕ) :
    ∃ H : RGraph (Fin n) r, (¬ ∃ f, F.IsEmbedding H f) ∧
      H.edges.card = extremalNumber F n := by
  classical
  unfold extremalNumber
  exact Nat.findGreatest_spec
    (P := fun m => ∃ H : RGraph (Fin n) r,
      (¬ ∃ f, F.IsEmbedding H f) ∧ H.edges.card = m)
    (Nat.zero_le (n.choose r)) ⟨empty (Fin n) r, F.empty_is_free hm, rfl⟩

/-- Pull a host back along an injective vertex map. -/
def pullback {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V]
    {r : ℕ} (H : RGraph W r) (f : V ↪ W) : RGraph V r := by
  classical
  exact ⟨(Finset.univ.powersetCard r).filter (fun e => e.map f ∈ H.edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

theorem embedding_pullback {U V W : Type*}
    [DecidableEq U] [DecidableEq V] [DecidableEq W] [Fintype V]
    {r : ℕ} (F : RGraph U r) (H : RGraph W r) (f : V ↪ W)
    {g : U → V} (hg : F.IsEmbedding (H.pullback f) g) :
    F.IsEmbedding H (f ∘ g) := by
  classical
  refine ⟨f.injective.comp hg.1, ?_⟩
  intro e he
  have h := (Finset.mem_filter.mp (hg.2 e he)).2
  simpa [Finset.map_eq_image, Finset.image_image] using h

theorem pullback_edges_card {V W : Type*}
    [DecidableEq V] [DecidableEq W] [Fintype V]
    {r : ℕ} (H : RGraph W r) (f : V ↪ W) :
    (H.pullback f).edges.card =
      (H.edges.filter (fun e => ∀ x ∈ e, x ∈ Set.range f)).card := by
  classical
  have hmap : (H.pullback f).edges.image (fun e => e.map f) =
      H.edges.filter (fun e => ∀ x ∈ e, x ∈ Set.range f) := by
    ext e
    constructor
    · rintro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).2, ?_⟩
      intro x hx
      obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hx
      exact ⟨v, hv⟩
    · intro he
      obtain ⟨he, hrange⟩ := Finset.mem_filter.mp he
      let d := e.preimage f f.injective.injOn
      have him : d.map f = e := by
        rw [Finset.map_eq_image, Finset.image_preimage]
        exact Finset.filter_true_of_mem (fun x hx => hrange x hx)
      have hd : d.card = r := by
        calc
          d.card = (d.map f).card := (Finset.card_map _).symm
          _ = e.card := congrArg Finset.card him
          _ = r := H.uniform e he
      exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hd⟩, by rw [him]; exact he⟩, him⟩
  calc
    (H.pullback f).edges.card = ((H.pullback f).edges.image (fun e => e.map f)).card :=
      (Finset.card_image_of_injective _ (Finset.map_injective f)).symm
    _ = _ := congrArg Finset.card hmap

theorem delete_vertex_card_le {r k n : ℕ} (F : RGraph (Fin k) r)
    (H : RGraph (Fin (n + 1)) r) (hfree : ¬ ∃ f, F.IsEmbedding H f)
    (v : Fin (n + 1)) :
    (H.edges.filter (fun e => v ∉ e)).card ≤ extremalNumber F n := by
  classical
  have hfree' : ¬ ∃ g, F.IsEmbedding (H.pullback (Fin.succAboveEmb v)) g := by
    rintro ⟨g, hg⟩
    exact hfree ⟨_, F.embedding_pullback H (Fin.succAboveEmb v) hg⟩
  have hcard : (H.pullback (Fin.succAboveEmb v)).edges.card =
      (H.edges.filter (fun e => v ∉ e)).card := by
    rw [H.pullback_edges_card]
    congr 1
    ext e
    simp only [Finset.mem_filter, Fin.succAboveEmb, Fin.range_succAbove,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    aesop
  rw [← hcard]
  exact F.edge_card_le_extremalNumber _ hfree'

/-- Each edge survives deletion of exactly n+1-r vertices. -/
theorem sum_deleted_edge_counts {r n : ℕ} (H : RGraph (Fin (n + 1)) r) :
    (∑ v : Fin (n + 1), (H.edges.filter (fun e => v ∉ e)).card) =
      (n + 1 - r) * H.edges.card := by
  classical
  have hinner : ∀ e ∈ H.edges,
      (∑ v : Fin (n + 1), if v ∉ e then (1 : ℕ) else 0) = (n + 1 - r : ℕ) := by
    intro e he
    have hf : (Finset.univ.filter (fun v : Fin (n + 1) => v ∉ e)) =
        Finset.univ \ e := by ext v; simp
    rw [Finset.sum_boole, hf, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin, H.uniform e he]
    simp
  calc
    (∑ v : Fin (n + 1), (H.edges.filter (fun e => v ∉ e)).card) =
        ∑ e ∈ H.edges, ∑ v : Fin (n + 1), if v ∉ e then (1 : ℕ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ H.edges, (n + 1 - r) := Finset.sum_congr rfl hinner
    _ = (n + 1 - r) * H.edges.card := by simp [mul_comm]

end RGraph

theorem extremalNumber_le_choose {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) :
    extremalNumber F n ≤ n.choose r := by
  classical
  exact Nat.findGreatest_le _

theorem extremalDensity_nonneg {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) :
    0 ≤ extremalDensity F n := by unfold extremalDensity; positivity

theorem extremalDensity_le_one {r k : ℕ} (F : RGraph (Fin k) r)
    {n : ℕ} (hn : r ≤ n) : extremalDensity F n ≤ 1 := by
  have hp : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply (div_le_iff₀ hp).mpr
  simpa using (Nat.cast_le.mpr (extremalNumber_le_choose F n) :
    (extremalNumber F n : ℝ) ≤ n.choose r)

theorem extremalNumber_delete_bound {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) (n : ℕ) :
    (n + 1 - r) * extremalNumber F (n + 1) ≤ (n + 1) * extremalNumber F n := by
  classical
  obtain ⟨H, hfree, hcard⟩ := F.exists_extremal hm (n + 1)
  rw [← hcard, ← H.sum_deleted_edge_counts]
  calc
    _ ≤ ∑ _v : Fin (n + 1), extremalNumber F n :=
      Finset.sum_le_sum (fun v _ => F.delete_vertex_card_le H hfree v)
    _ = _ := by simp

theorem extremalDensity_succ_le {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) {n : ℕ} (hn : r ≤ n) :
    extremalDensity F (n + 1) ≤ extremalDensity F n := by
  have hp0 : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hp1 : (0 : ℝ) < (n + 1).choose r := by
    exact_mod_cast Nat.choose_pos (show r ≤ n + 1 by omega)
  have ha : (0 : ℝ) < (n + 1 - r : ℕ) := by
    exact_mod_cast (show 0 < n + 1 - r by omega)
  have hc : (n + 1 - r : ℕ) * (extremalNumber F (n + 1) : ℝ) ≤
      (n + 1 : ℕ) * (extremalNumber F n : ℝ) := by
    exact_mod_cast extremalNumber_delete_bound F hm n
  have hchoose : (n.choose r : ℝ) * (n + 1 : ℕ) =
      ((n + 1).choose r : ℝ) * (n + 1 - r : ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n r
  have hmul := mul_le_mul_of_nonneg_right hc hp0.le
  have hchoose' := congrArg (fun x : ℝ => x * (extremalNumber F n : ℝ)) hchoose
  apply (div_le_div_iff₀ hp1 hp0).mpr
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith [hmul, hchoose']

/-- The Katona--Nemetz--Simonovits limit-existence theorem, for every finite
forbidden hypergraph with at least one edge. -/
theorem extremalDensity_tendsto {r k : ℕ} (F : RGraph (Fin k) r)
    (hm : 1 ≤ F.edges.card) :
    Tendsto (extremalDensity F) atTop (𝓝 (turanDensity F)) := by
  have hanti : Antitone (fun n : ℕ => extremalDensity F (n + r)) :=
    antitone_nat_of_succ_le (fun n => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        extremalDensity_succ_le F hm (show r ≤ n + r by omega))
  have hbdd : BddBelow (Set.range (fun n : ℕ => extremalDensity F (n + r))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact extremalDensity_nonneg F _⟩
  exact (tendsto_add_atTop_iff_nat r).mp (tendsto_atTop_ciInf hanti hbdd)

end
end ImprovedSidorenko
