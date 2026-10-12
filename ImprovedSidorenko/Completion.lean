module

public import ImprovedSidorenko.Independence
public import ImprovedSidorenko.EdgePotential
public import ImprovedSidorenko.LocalLemma

@[expose] public section

/-!
# Completing an actual partial hypergraph embedding

The independent-coordinate hypothesis of the local lemma is proved here using
`Independence.lean`.  Thus `local_completion` is Claim 2.4 for the concrete
finite hypergraph definitions, not a conditional appeal to an unproved LLL.
-/

open scoped BigOperators

namespace ImprovedSidorenko

universe u v

section SupportedEvents

variable {V : Type u} {W : Type v} {I : Type*}
  [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype W] [Nonempty W]

/-- A family of non-neighbours uses coordinates disjoint from the given event. -/
theorem support_disjoint_nonneighbors (edges : Finset I) (support : I → Finset V)
    (i : I) (S : Finset I) (hS : S ⊆ edges) (hiS : i ∉ S)
    (hdis : Disjoint S (LocalLemma.neighbors edges support i)) :
    Disjoint (support i) (S.biUnion support) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvi hvS
  obtain ⟨j, hjS, hvj⟩ := Finset.mem_biUnion.mp hvS
  have hji : j ≠ i := by
    intro h
    exact hiS (h ▸ hjS)
  have hjN : j ∈ LocalLemma.neighbors edges support i := by
    exact Finset.mem_filter.mpr ⟨hS hjS, hji, v, hvi, hvj⟩
  exact Finset.disjoint_left.mp hdis hjS hjN

/-- The support version of Claim 2.4 with all independence obligations discharged. -/
theorem completion_of_small_supported_load
    (edges : Finset I) (support : I → Finset V) (bad : I → (V → W) → Prop)
    (r : ℝ) (hr : 1 ≤ r) (m : ℕ) (hm : edges.card ≤ m)
    (hsupport : ∀ i ∈ edges, EventSupported (bad i) (support i))
    (hload : ∀ v,
      LocalLemma.vertexLoad edges support (fun i => eventProb (bad i)) v < 1 / (4 * r))
    (hne : ∀ i ∈ edges, (support i).Nonempty)
    (hcard : ∀ i ∈ edges, ((support i).card : ℝ) ≤ r) :
    (1 - 1 / (2 * r)) ^ m ≤ eventProb (LocalLemma.avoidEvents bad edges) := by
  apply LocalLemma.small_load_completion_of_dependency edges support bad r hr m hm hload hne hcard
  intro i hi S hS hiS hdis
  apply eventProb_inter_of_disjoint_support (bad i) (LocalLemma.avoidEvents bad S)
    (support i) (S.biUnion support)
    (support_disjoint_nonneighbors edges support i S hS hiS hdis) (hsupport i hi)
  exact EventSupported.forall_finset S (fun i g => ¬ bad i g) support
    (fun i hi => (hsupport i (hS hi)).not)

end SupportedEvents

namespace RGraph

variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [Nonempty W] {r : ℕ}

def unfinished (F : RGraph V r) (A : Finset V) : Finset (Finset V) :=
  F.edges.filter (fun e => (e \ A).Nonempty)

theorem unfinished_subset (F : RGraph V r) (A : Finset V) :
    F.unfinished A ⊆ F.edges := Finset.filter_subset _ _

theorem unfinished_vertexLoad (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ : V → W) (v : V) :
    LocalLemma.vertexLoad (F.unfinished A) (fun e => e \ A)
      (fun e => eventProb (H.badEvent A φ e)) v =
        if v ∈ A then 0 else F.load H A φ v := by
  classical
  simp only [LocalLemma.vertexLoad, badEvent_probability]
  unfold unfinished
  rw [Finset.sum_filter]
  by_cases hv : v ∈ A
  · simp [hv]
  · simp only [ite_eq_right hv]
    unfold load
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : v ∈ e
    · have hne : (e \ A).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨he, hv⟩⟩
      simp [he, hv, hne]
    · simp [he, hv]

/-- Avoiding all unfinished failures preserves every original edge of a legal map. -/
theorem all_edges_successful_of_avoid (F : RGraph V r) (H : RGraph W r)
    (A : Finset V) (φ g : V → W) (hlegal : H.Legal A φ)
    (havoid : LocalLemma.avoidEvents (H.badEvent A φ) (F.unfinished A) g) :
    ∀ e ∈ F.edges, e.image (fill A φ g) ∈ H.edges := by
  classical
  intro e he
  by_cases hun : (e \ A).Nonempty
  · have hb := havoid e (Finset.mem_filter.mpr ⟨he, hun⟩)
    exact (not_not.mp hb).1
  · have hsub : e ⊆ A := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hun)
    have himage : e.image (fill A φ g) = e.image φ := by
      apply Finset.image_congr
      intro v hv
      exact fill_of_mem A φ g (hsub hv)
    rw [himage]
    exact (legal_completed_edge F H hlegal he hsub).1

/-- Claim 2.4 for the actual independent random extension of a legal partial map. -/
theorem local_completion (F : RGraph V r) (H : RGraph W r) (hr : 1 ≤ r)
    (A : Finset V) (φ : V → W) (hlegal : H.Legal A φ)
    (hload : ∀ v, v ∉ A → F.load H A φ v < 1 / (4 * (r : ℝ))) :
    (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card ≤
      eventProb (fun g : V → W => ∀ e ∈ F.edges, e.image (fill A φ g) ∈ H.edges) := by
  classical
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmain := completion_of_small_supported_load
    (F.unfinished A) (fun e => e \ A) (H.badEvent A φ) (r : ℝ) hr'
    F.edges.card (Finset.card_le_card (F.unfinished_subset A))
    (fun e _ => H.badEvent_supported A φ e)
    (by
      intro v
      rw [F.unfinished_vertexLoad H A φ v]
      by_cases hv : v ∈ A
      · simp only [ite_eq_left hv]
        positivity
      · simpa only [ite_eq_right hv] using hload v hv)
    (fun e he => (Finset.mem_filter.mp he).2)
    (by
      intro e he
      exact_mod_cast F.remaining_le A (F.unfinished_subset A he))
  exact hmain.trans (eventProb_mono (fun g hg =>
    F.all_edges_successful_of_avoid H A φ g hlegal hg))

/-- The full second stage: a legal small-load partial map extends to a copy of `F`. -/
theorem embedding_from_small_load (F : RGraph V r) (H : RGraph W r) (hr : 1 ≤ r)
    (A : Finset V) (φ : V → W) (hlegal : H.Legal A φ)
    (hload : ∀ v, v ∉ A → F.load H A φ v < 1 / (4 * (r : ℝ)))
    (hn : ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) <
      (1 - 1 / (2 * (r : ℝ))) ^ F.edges.card) :
    ∃ f : V → W, F.IsEmbedding H f := by
  apply embedding_of_success_probability F H A φ hlegal.1
  exact hn.trans_le (F.local_completion H hr A φ hlegal hload)

end RGraph
end ImprovedSidorenko
