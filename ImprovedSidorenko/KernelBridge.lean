module

public import ImprovedSidorenko.CliquePotential
public import ImprovedSidorenko.EdgePotential
public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Agreement of the two finite conditional-probability representations

The edge potential averages a full map, ignoring already assigned coordinates.
The clique potential recursively averages a list of independent host vertices.
This file proves that the two representations agree, using induction on the
number of unassigned vertices of an edge.
-/

open scoped BigOperators

namespace ImprovedSidorenko

namespace RGraph

universe u v

variable {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [Nonempty W] {r : ℕ}

omit [DecidableEq V] [Fintype V] [Nonempty W] in
theorem cliqueKernel_zero_eq_edgeFailure (H : RGraph W r) (e : Finset V) (φ : V → W) :
    H.cliqueKernel 0 (e.toList.map φ) = H.edgeFailure e φ := by
  classical
  have hnodup : (e.toList.map φ).Nodup ↔ Set.InjOn φ (e : Set V) := by
    rw [List.nodup_map_iff_inj_on (Finset.nodup_toList e)]
    simp only [Finset.mem_toList, Set.InjOn, Finset.mem_coe]
  have hset : (e.toList.map φ).toFinset = e.image φ := by
    ext w
    simp
  simp only [cliqueKernel_zero, edgeFailure, hset, hnodup, and_comm]

theorem failureProb_of_subset (H : RGraph W r) (A : Finset V) (φ : V → W)
    (e : Finset V) (he : e ⊆ A) : H.failureProb A φ e = H.edgeFailure e φ := by
  have hfill : ∀ g : V → W, H.edgeFailure e (fill A φ g) = H.edgeFailure e φ := by
    intro g
    apply H.edgeFailure_congr
    intro w hw
    exact fill_of_mem A φ g (he hw)
  simp only [failureProb, hfill, Fintype.expect_const]

theorem failureProb_eq_cliqueKernel_aux (H : RGraph W r) (n : ℕ) :
    ∀ (A : Finset V) (φ : V → W) (e : Finset V), (e \ A).card = n →
      H.failureProb A φ e =
        H.cliqueKernel (e \ A).card ((e ∩ A).toList.map φ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A φ e hn
      by_cases hn0 : n = 0
      · have hcard0 : (e \ A).card = 0 := hn.trans hn0
        have hsub : e ⊆ A := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard0)
        rw [hcard0, Finset.inter_eq_left.mpr hsub, H.failureProb_of_subset A φ e hsub]
        exact (H.cliqueKernel_zero_eq_edgeFailure e φ).symm
      · have hpos : 0 < (e \ A).card := by rw [hn]; omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        obtain ⟨hve, hvA⟩ := Finset.mem_sdiff.mp hv
        have hdiff : e \ insert v A = (e \ A).erase v := by
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        have hcard : (e \ insert v A).card + 1 = n := by
          rw [hdiff, Finset.card_erase_of_mem hv, hn]
          omega
        have hlt : (e \ insert v A).card < n := by omega
        have hknown : e ∩ insert v A = insert v (e ∩ A) := by
          ext w
          by_cases hw : w = v
          · subst w; simp [hve]
          · simp [hw]
        have hvknown : v ∉ e ∩ A := by simp [hvA]
        calc
          H.failureProb A φ e
              = 𝔼 x : W, H.failureProb (insert v A) (Function.update φ v x) e :=
                (H.failureProb_tower A φ e hvA).symm
          _ = 𝔼 x : W, H.cliqueKernel (e \ insert v A).card
              (x :: (e ∩ A).toList.map φ) := by
                apply Finset.expect_congr rfl
                intro x _
                rw [ih _ hlt (insert v A) (Function.update φ v x) e rfl]
                have hp := (Finset.toList_insert hvknown).map (Function.update φ v x)
                have hp' : ((e ∩ insert v A).toList.map (Function.update φ v x)).Perm
                    (x :: (e ∩ A).toList.map φ) := by
                  simpa only [hknown, List.map_cons, Function.update_self,
                    map_toList_update_of_not_mem (e ∩ A) φ hvknown x] using hp
                exact H.cliqueKernel_perm _ hp'
          _ = H.cliqueKernel ((e \ insert v A).card + 1) ((e ∩ A).toList.map φ) :=
                (H.cliqueKernel_succ _ _).symm
          _ = H.cliqueKernel (e \ A).card ((e ∩ A).toList.map φ) := by rw [hcard, hn]

/-- The complete bridge; no uniformity hypothesis on the source subset is
needed, since both representations use the same terminal host-edge test. -/
theorem failureProb_eq_cliqueKernel (H : RGraph W r)
    (A : Finset V) (φ : V → W) (e : Finset V) :
    H.failureProb A φ e =
      H.cliqueKernel (e \ A).card ((e ∩ A).toList.map φ) :=
  H.failureProb_eq_cliqueKernel_aux _ A φ e rfl

/-- All source edges of size `r` have the same unconditional failure probability. -/
theorem failureProb_empty (H : RGraph W r) (φ : V → W) (e : Finset V)
    (he : e.card = r) : H.failureProb ∅ φ e = H.cliqueKernel r [] := by
  rw [H.failureProb_eq_cliqueKernel]
  simp [he]

/-- The initial edge potential is exactly `r m` times the host failure density. -/
theorem edgePotential_empty (F : RGraph V r) (H : RGraph W r) (φ : V → W) :
    F.edgePotential H ∅ φ =
      (r : ℝ) * F.edges.card * H.cliqueKernel r [] := by
  unfold edgePotential
  calc
    (∑ e ∈ F.edges, (remaining ∅ e : ℝ) * H.failureProb ∅ φ e)
        = ∑ e ∈ F.edges, (r : ℝ) * H.cliqueKernel r [] := by
          apply Finset.sum_congr rfl
          intro e he
          rw [H.failureProb_empty φ e (F.uniform e he)]
          simp [remaining, F.uniform e he]
    _ = (r : ℝ) * F.edges.card * H.cliqueKernel r [] := by
          simp [nsmul_eq_mul]
          ring

end RGraph

end ImprovedSidorenko
