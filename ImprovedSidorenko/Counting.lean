module

public import ImprovedSidorenko.KernelBridge
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-!
# The exact density of successful ordered edge samples

An injective ordered sample whose image is a host edge is the same data as a
host edge together with a bijection from `Fin r` to that edge.  Thus each edge
contributes exactly `r!` successful samples.  Combining this finite count with
the verified conditional-probability bridge identifies the initial clique
kernel with the usual host deficit.
-/

open scoped BigOperators

namespace ImprovedSidorenko.RGraph

universe u

variable {W : Type u} [DecidableEq W] {r : ℕ}

/-- A bijective labelling has precisely the labelled edge as its image. -/
theorem edge_labelling_image (e : Finset W) (σ : Fin r ≃ ↥e) :
    Finset.univ.image (fun i => (σ i).1) = e := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
    exact hiw ▸ (σ i).2
  · intro hw
    obtain ⟨i, hi⟩ := σ.surjective ⟨w, hw⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, congrArg Subtype.val hi⟩

/-- Successful ordered samples are edges equipped with bijective labellings. -/
noncomputable def orderedEdgeEquiv (H : RGraph W r) :
    {g : Fin r → W // Finset.univ.image g ∈ H.edges ∧ Function.Injective g} ≃
      (Σ e : ↥H.edges, (Fin r ≃ ↥e.1)) := by
  classical
  let backward : (Σ e : ↥H.edges, (Fin r ≃ ↥e.1)) →
      {g : Fin r → W // Finset.univ.image g ∈ H.edges ∧ Function.Injective g} :=
    fun a => ⟨fun i => (a.2 i).1, by
      constructor
      · rw [edge_labelling_image a.1.1 a.2]
        exact a.1.2
      · intro i j hij
        exact a.2.injective (Subtype.ext hij)⟩
  have hinj : Function.Injective backward := by
    rintro ⟨e, σ⟩ ⟨f, τ⟩ h
    have hfun : (fun i => (σ i).1) = fun i => (τ i).1 := congrArg Subtype.val h
    have hef : e = f := by
      apply Subtype.ext
      calc
        e.1 = Finset.univ.image (fun i => (σ i).1) := (edge_labelling_image e.1 σ).symm
        _ = Finset.univ.image (fun i => (τ i).1) :=
          congrArg (fun g : Fin r → W => Finset.univ.image g) hfun
        _ = f.1 := edge_labelling_image f.1 τ
    subst f
    have hστ : σ = τ := by
      apply Equiv.ext
      intro i
      exact Subtype.ext (congrFun hfun i)
    subst τ
    rfl
  have hsurj : Function.Surjective backward := by
    rintro ⟨g, hg, hginj⟩
    let e : ↥H.edges := ⟨Finset.univ.image g, hg⟩
    let forward : Fin r → ↥e.1 :=
      fun i => ⟨g i, Finset.mem_image_of_mem g (Finset.mem_univ i)⟩
    have hforward : Function.Bijective forward := by
      constructor
      · intro i j hij
        exact hginj (congrArg Subtype.val hij)
      · rintro ⟨w, hw⟩
        obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
        exact ⟨i, Subtype.ext hiw⟩
    refine ⟨⟨e, Equiv.ofBijective forward hforward⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact (Equiv.ofBijective backward ⟨hinj, hsurj⟩).symm

/-- Each host edge contributes exactly `r!` injective ordered samples. -/
theorem ordered_edge_maps_card [Fintype W] (H : RGraph W r) :
    Fintype.card {g : Fin r → W //
      Finset.univ.image g ∈ H.edges ∧ Function.Injective g} =
        r.factorial * H.edges.card := by
  classical
  rw [Fintype.card_congr (H.orderedEdgeEquiv), Fintype.card_sigma]
  have he : ∀ e : ↥H.edges, Fintype.card (Fin r ≃ ↥e.1) = r.factorial := by
    intro e
    have hc : Fintype.card (Fin r) = Fintype.card ↥e.1 := by
      simp [H.uniform e.1 e.2]
    simpa using Fintype.card_equiv (Fintype.equivOfCardEq hc)
  simp_rw [he]
  simp [mul_comm]

/-- The actual initial clique-failure probability equals the host deficit. -/
theorem cliqueKernel_empty_eq_density [Fintype W] [Nonempty W] (H : RGraph W r) :
    H.cliqueKernel r [] =
      1 - (r.factorial : ℝ) * (H.edges.card : ℝ) / (Fintype.card W : ℝ) ^ r := by
  classical
  let φ : Fin r → W := fun _ => Classical.choice ‹Nonempty W›
  let Good : (Fin r → W) → Prop :=
    fun g => Finset.univ.image g ∈ H.edges ∧ Function.Injective g
  have hfail (g : Fin r → W) :
      H.edgeFailure Finset.univ (fill ∅ φ g) =
        (1 : ℝ) - (if Good g then 1 else 0) := by
    have hfill : fill ∅ φ g = g := by
      funext i
      simp [fill]
    have hinj : Set.InjOn g (↑(Finset.univ : Finset (Fin r))) ↔ Function.Injective g := by
      simp [Set.InjOn, Function.Injective]
    rw [hfill]
    simp only [edgeFailure, hinj]
    change (if Good g then (0 : ℝ) else 1) = 1 - (if Good g then 1 else 0)
    split_ifs <;> norm_num
  have hcount : Fintype.card {g : Fin r → W // Good g} =
      r.factorial * H.edges.card := H.ordered_edge_maps_card
  rw [← H.failureProb_empty φ Finset.univ (by simp)]
  unfold failureProb
  simp_rw [hfail]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]
  congr 1
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole, ← Fintype.card_subtype Good, hcount]
  simp [Fintype.card_fun, Nat.cast_mul, Nat.cast_pow]

end ImprovedSidorenko.RGraph
