module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Tactic
public import ImprovedSidorenko.Collision

@[expose] public section

/-!
# The local-lemma estimates in Claim 2.4

This module first verifies the finite weighted-neighbourhood argument used in
the paper.  A support is the set of still-unassigned coordinates on which an
unfinished edge depends.  The probability input consists of nonnegative edge
weights and the small vertex-load inequalities.
-/

open scoped BigOperators

namespace ImprovedSidorenko.LocalLemma

variable {I V : Type*} [DecidableEq I] [DecidableEq V]

/-- The elementary finite product estimate used in the local lemma. -/
theorem one_sub_sum_le_prod (s : Finset I) (x : I → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hx0 a (Finset.mem_insert_self a s)
    have ha1 := hx1 a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hs0
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    calc
      1 - (x a + ∑ i ∈ s, x i) ≤ (1 - x a) * (1 - ∑ i ∈ s, x i) := by
        nlinarith [mul_nonneg ha0 hsum]
      _ ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) :=
        mul_le_mul_of_nonneg_left (ih hs0 hs1) (sub_nonneg.mpr ha1)

/-- The unfinished-edge load at a single unassigned vertex. -/
def vertexLoad (edges : Finset I) (support : I → Finset V) (p : I → ℝ) (v : V) : ℝ :=
  ∑ e ∈ edges, if v ∈ support e then p e else 0

/-- Distinct unfinished edges are neighbours when they share a coordinate. -/
def neighbors (edges : Finset I) (support : I → Finset V) (e : I) : Finset I :=
  edges.filter (fun f => f ≠ e ∧ ∃ v ∈ support e, v ∈ support f)

theorem neighbors_subset (edges : Finset I) (support : I → Finset V) (e : I) :
    neighbors edges support e ⊆ edges := Finset.filter_subset _ _

theorem self_not_mem_neighbors (edges : Finset I) (support : I → Finset V) (e : I) :
    e ∉ neighbors edges support e := by simp [neighbors]

theorem edge_weight_le_vertexLoad (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (hp : ∀ e ∈ edges, 0 ≤ p e)
    {e : I} (he : e ∈ edges) {v : V} (hv : v ∈ support e) :
    p e ≤ vertexLoad edges support p v := by
  have h := Finset.single_le_sum
    (f := fun f => if v ∈ support f then p f else 0)
    (fun f hf => by
      split_ifs
      · exact hp f hf
      · exact le_rfl) he
  simpa [vertexLoad, hv] using h

/-- Every neighbour weight is charged to one or more shared coordinates. -/
theorem neighbor_sum_le_load_sum (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (hp : ∀ e ∈ edges, 0 ≤ p e) (e : I) :
    ∑ f ∈ neighbors edges support e, p f ≤
      ∑ v ∈ support e, vertexLoad edges support p v := by
  calc
    ∑ f ∈ neighbors edges support e, p f ≤
        ∑ f ∈ neighbors edges support e, ∑ v ∈ support e,
          if v ∈ support f then p f else 0 := by
      apply Finset.sum_le_sum
      intro f hf
      obtain ⟨hfE, hfe, v, hv, hvf⟩ := Finset.mem_filter.mp hf
      have h := Finset.single_le_sum
        (f := fun w => if w ∈ support f then p f else 0)
        (fun w hw => by
          split_ifs
          · exact hp f hfE
          · exact le_rfl) hv
      simpa [hvf] using h
    _ = ∑ v ∈ support e, ∑ f ∈ neighbors edges support e,
          if v ∈ support f then p f else 0 := Finset.sum_comm
    _ ≤ ∑ v ∈ support e, vertexLoad edges support p v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum_of_subset_of_nonneg (neighbors_subset edges support e)
        (fun f hf hfn => by split_ifs; exact hp f hf; exact le_rfl)

/-- Small vertex loads and support size at most `r` give the `1/4` bound. -/
theorem neighbor_sum_le_quarter (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (r : ℝ) (hr : 0 < r)
    (hp : ∀ f ∈ edges, 0 ≤ p f)
    (hload : ∀ v, vertexLoad edges support p v < 1 / (4 * r))
    (e : I) (hcard : ((support e).card : ℝ) ≤ r) :
    ∑ f ∈ neighbors edges support e, p f ≤ (1 / 4 : ℝ) := by
  calc
    ∑ f ∈ neighbors edges support e, p f ≤
        ∑ v ∈ support e, vertexLoad edges support p v :=
      neighbor_sum_le_load_sum edges support p hp e
    _ ≤ ∑ v ∈ support e, 1 / (4 * r) :=
      Finset.sum_le_sum (fun v hv => (hload v).le)
    _ = ((support e).card : ℝ) * (1 / (4 * r)) := by simp
    _ ≤ r * (1 / (4 * r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 / 4 := by field_simp [ne_of_gt hr]

/-- A nonempty support gives the individual weight bound. -/
theorem doubled_edge_weight_lt (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (r : ℝ) (hr : 0 < r)
    (hp : ∀ f ∈ edges, 0 ≤ p f)
    (hload : ∀ v, vertexLoad edges support p v < 1 / (4 * r))
    {e : I} (he : e ∈ edges) (hne : (support e).Nonempty) :
    2 * p e < 1 / (2 * r) := by
  obtain ⟨v, hv⟩ := hne
  have h := lt_of_le_of_lt (edge_weight_le_vertexLoad edges support p hp he hv) (hload v)
  have hident : 2 * (1 / (4 * r)) = 1 / (2 * r) := by field_simp [ne_of_gt hr]; norm_num
  linarith

/-- The substitution `x_e = 2 p_e` verifies the asymmetric LLL inequality. -/
theorem doubled_weights_satisfy_lll (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (r : ℝ) (hr : 1 ≤ r)
    (hp : ∀ f ∈ edges, 0 ≤ p f)
    (hload : ∀ v, vertexLoad edges support p v < 1 / (4 * r))
    (hne : ∀ f ∈ edges, (support f).Nonempty)
    (hcard : ∀ f ∈ edges, ((support f).card : ℝ) ≤ r)
    {e : I} (he : e ∈ edges) :
    0 ≤ 2 * p e ∧ 2 * p e < 1 ∧
      p e ≤ (2 * p e) * ∏ f ∈ neighbors edges support e, (1 - 2 * p f) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hhalf : 1 / (2 * r) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
    linarith
  have hx : ∀ f ∈ edges, 2 * p f < 1 := by
    intro f hf
    have := doubled_edge_weight_lt edges support p r hr0 hp hload hf (hne f hf)
    linarith
  have hsum := neighbor_sum_le_quarter edges support p r hr0 hp hload e (hcard e he)
  have hprod := one_sub_sum_le_prod (neighbors edges support e) (fun f => 2 * p f)
    (fun f hf => mul_nonneg (by norm_num) (hp f (neighbors_subset edges support e hf)))
    (fun f hf => (hx f (neighbors_subset edges support e hf)).le)
  have hsum2 : (∑ f ∈ neighbors edges support e, 2 * p f) ≤ (1 / 2 : ℝ) := by
    rw [← Finset.mul_sum]
    linarith
  have hprodHalf : (1 / 2 : ℝ) ≤ ∏ f ∈ neighbors edges support e, (1 - 2 * p f) := by
    linarith
  refine ⟨mul_nonneg (by norm_num) (hp e he), hx e he, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hprodHalf
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hp e he))
  nlinarith

/-- There are at most `m` unfinished edges, giving the precise product in Claim 2.4. -/
theorem completion_product_lower_bound (edges : Finset I) (support : I → Finset V)
    (p : I → ℝ) (r : ℝ) (hr : 1 ≤ r) (m : ℕ) (hm : edges.card ≤ m)
    (hp : ∀ f ∈ edges, 0 ≤ p f)
    (hload : ∀ v, vertexLoad edges support p v < 1 / (4 * r))
    (hne : ∀ f ∈ edges, (support f).Nonempty) :
    (1 - 1 / (2 * r)) ^ m ≤ ∏ f ∈ edges, (1 - 2 * p f) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb0 : 0 ≤ 1 - 1 / (2 * r) := by
    have hhalf : 1 / (2 * r) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
      linarith
    linarith
  have hb1 : 1 - 1 / (2 * r) ≤ (1 : ℝ) := by
    have hdiv : 0 ≤ 1 / (2 * r) := by positivity
    linarith
  calc
    (1 - 1 / (2 * r)) ^ m ≤ (1 - 1 / (2 * r)) ^ edges.card :=
      pow_le_pow_of_le_one hb0 hb1 hm
    _ = ∏ f ∈ edges, (1 - 1 / (2 * r)) := by simp
    _ ≤ ∏ f ∈ edges, (1 - 2 * p f) := by
      apply Finset.prod_le_prod₀ (fun f hf => hb0)
      intro f hf
      have h := doubled_edge_weight_lt edges support p r hr0 hp hload hf (hne f hf)
      linarith

/-!
## A finite asymmetric Lovász Local Lemma

The following proof uses the probabilities `G S` of avoiding the events in a
finite index set `S`.  The auxiliary abstract statement assumes only the
elementary monotonicity of a bad-event intersection and independence from the
non-neighbours.  Below these elementary properties are connected to actual
finite sample-space probabilities; the local lemma itself is proved here.
-/

/-- Removing factors in `[0,1]` can only increase a finite product. -/
theorem prod_antitone_of_mem_unit_interval (a : I → ℝ) {s t : Finset I}
    (hst : s ⊆ t) (ha0 : ∀ i ∈ t, 0 ≤ a i) (ha1 : ∀ i ∈ t, a i ≤ 1) :
    ∏ i ∈ t, a i ≤ ∏ i ∈ s, a i := by
  rw [← Finset.prod_sdiff hst]
  have hd : ∏ i ∈ t \ s, a i ≤ 1 :=
    Finset.prod_le_one₀
      (fun i hi => ha0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => ha1 i (Finset.mem_sdiff.mp hi).1)
  have hs : 0 ≤ ∏ i ∈ s, a i :=
    Finset.prod_nonneg (fun i hi => ha0 i (hst hi))
  simpa using mul_le_mul_of_nonneg_right hd hs

/-- Multiply the one-event extension inequalities, starting from `base`. -/
theorem product_extension_lower_bound (G : Finset I → ℝ) (a : I → ℝ)
    (base added : Finset I) (hdis : Disjoint base added)
    (ha : ∀ i ∈ added, 0 ≤ a i)
    (hstep : ∀ S ⊆ base ∪ added, ∀ i ∈ added, i ∉ S →
      a i * G S ≤ G (insert i S)) :
    G base * (∏ i ∈ added, a i) ≤ G (base ∪ added) := by
  induction added using Finset.induction_on with
  | empty => simp
  | @insert i added hi ih =>
    have hdis' : Disjoint base added := hdis.mono_right (Finset.subset_insert _ _)
    have ha' : ∀ j ∈ added, 0 ≤ a j :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hsub : base ∪ added ⊆ base ∪ insert i added := by
      intro j hj
      exact Finset.mem_union.mpr <| (Finset.mem_union.mp hj).imp_right
        (fun h => Finset.mem_insert_of_mem h)
    have hstep' : ∀ S ⊆ base ∪ added, ∀ j ∈ added, j ∉ S →
        a j * G S ≤ G (insert j S) := by
      intro S hS j hj hjS
      exact hstep S (hS.trans hsub) j (Finset.mem_insert_of_mem hj) hjS
    have hiBase : i ∉ base := by
      intro h
      exact Finset.disjoint_left.mp hdis h (Finset.mem_insert_self i added)
    have hiUnion : i ∉ base ∪ added := by simp [hiBase, hi]
    have hlast := hstep (base ∪ added) hsub i (Finset.mem_insert_self i added) hiUnion
    have heq : insert i (base ∪ added) = base ∪ insert i added := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    rw [Finset.prod_insert hi]
    calc
      G base * (a i * ∏ j ∈ added, a j) = a i * (G base * ∏ j ∈ added, a j) := by ring
      _ ≤ a i * G (base ∪ added) :=
        mul_le_mul_of_nonneg_left (ih hdis' ha' hstep') (ha i (Finset.mem_insert_self i added))
      _ ≤ G (base ∪ insert i added) := by
        rw [heq] at hlast
        exact hlast

/-- The induction step in the asymmetric local lemma.

`G S - G (insert i S)` is the probability that event `i` occurs while all
events in `S` are avoided.  `hmono` is just monotonicity of that intersection.
`hindep` is the dependency-graph hypothesis, in its (slightly more general)
one-sided form.
-/
theorem finite_local_lemma_step (edges : Finset I) (G : Finset I → ℝ)
    (p x : I → ℝ) (N : I → Finset I)
    (hG0 : ∀ S, 0 ≤ G S)
    (hmono : ∀ i S T, T ⊆ S →
      G S - G (insert i S) ≤ G T - G (insert i T))
    (hN : ∀ i ∈ edges, N i ⊆ edges)
    (hx0 : ∀ i ∈ edges, 0 ≤ x i) (hx1 : ∀ i ∈ edges, x i ≤ 1)
    (hbound : ∀ i ∈ edges, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hindep : ∀ i ∈ edges, ∀ S ⊆ edges, i ∉ S → Disjoint S (N i) →
      G S - G (insert i S) ≤ p i * G S) :
    ∀ S ⊆ edges, ∀ i ∈ edges, i ∉ S →
      (1 - x i) * G S ≤ G (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS i hi hiS
    let base := S \ N i
    let added := S ∩ N i
    have hbaseS : base ⊆ S := Finset.sdiff_subset
    have haddedS : added ⊆ S := Finset.inter_subset_left
    have haddedN : added ⊆ N i := Finset.inter_subset_right
    have hunion : base ∪ added = S := by
      ext j
      simp only [base, added, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hdis : Disjoint base added := by
      apply Finset.disjoint_left.mpr
      intro j hjb hja
      exact (Finset.mem_sdiff.mp hjb).2 (Finset.mem_inter.mp hja).2
    have hext : G base * (∏ j ∈ added, (1 - x j)) ≤ G S := by
      have hh := product_extension_lower_bound G (fun j => 1 - x j) base added hdis
        (fun j hj => sub_nonneg.mpr (hx1 j (hS (haddedS hj))))
        (by
          intro T hT j hj hjT
          have hTS : T ⊆ S := by simpa [hunion] using hT
          have hjS : j ∈ S := haddedS hj
          have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS, by
            intro hEq
            exact hjT (hEq.symm ▸ hjS)⟩
          exact ih T hstrict (hTS.trans hS) j (hS hjS) hjT)
      simpa [hunion] using hh
    have hprod : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ added, (1 - x j) :=
      prod_antitone_of_mem_unit_interval (fun j => 1 - x j) haddedN
        (fun j hj => sub_nonneg.mpr (hx1 j (hN i hi hj)))
        (fun j hj => by
          linarith [hx0 j (hN i hi hj)])
    have hiBase : i ∉ base := fun h => hiS (hbaseS h)
    have hbaseN : Disjoint base (N i) := Finset.sdiff_disjoint
    have hbad : G S - G (insert i S) ≤ x i * G S := by
      calc
        G S - G (insert i S) ≤ G base - G (insert i base) := hmono i S base hbaseS
        _ ≤ p i * G base := hindep i hi base (hbaseS.trans hS) hiBase hbaseN
        _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * G base :=
          mul_le_mul_of_nonneg_right (hbound i hi) (hG0 base)
        _ ≤ (x i * ∏ j ∈ added, (1 - x j)) * G base :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (hx0 i hi)) (hG0 base)
        _ = x i * (G base * ∏ j ∈ added, (1 - x j)) := by ring
        _ ≤ x i * G S := mul_le_mul_of_nonneg_left hext (hx0 i hi)
    nlinarith

/-- The full product lower bound of the finite asymmetric Lovász Local Lemma. -/
theorem finite_local_lemma (edges : Finset I) (G : Finset I → ℝ)
    (p x : I → ℝ) (N : I → Finset I)
    (hGempty : G ∅ = 1) (hG0 : ∀ S, 0 ≤ G S)
    (hmono : ∀ i S T, T ⊆ S →
      G S - G (insert i S) ≤ G T - G (insert i T))
    (hN : ∀ i ∈ edges, N i ⊆ edges)
    (hx0 : ∀ i ∈ edges, 0 ≤ x i) (hx1 : ∀ i ∈ edges, x i ≤ 1)
    (hbound : ∀ i ∈ edges, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hindep : ∀ i ∈ edges, ∀ S ⊆ edges, i ∉ S → Disjoint S (N i) →
      G S - G (insert i S) ≤ p i * G S) :
    (∏ i ∈ edges, (1 - x i)) ≤ G edges := by
  have hstep := finite_local_lemma_step edges G p x N hG0 hmono hN hx0 hx1 hbound hindep
  have h := product_extension_lower_bound G (fun i => 1 - x i) ∅ edges
    (by simp) (fun i hi => sub_nonneg.mpr (hx1 i hi))
    (by simpa only [Finset.empty_union] using hstep)
  simpa [hGempty] using h

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- All bad events indexed by `S` are avoided. -/
def avoidEvents (bad : I → Ω → Prop) (S : Finset I) (ω : Ω) : Prop :=
  ∀ i ∈ S, ¬ bad i ω

theorem avoidEvents_insert (bad : I → Ω → Prop) (S : Finset I) (i : I) (ω : Ω) :
    avoidEvents bad (insert i S) ω ↔ ¬ bad i ω ∧ avoidEvents bad S ω := by
  simp [avoidEvents]

/-- Splitting according to one bad event is an identity of actual probabilities. -/
theorem eventProb_avoid_difference (bad : I → Ω → Prop) (S : Finset I) (i : I) :
    eventProb (avoidEvents bad S) - eventProb (avoidEvents bad (insert i S)) =
      eventProb (fun ω => bad i ω ∧ avoidEvents bad S ω) := by
  classical
  unfold eventProb
  rw [← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro ω hω
  rw [show avoidEvents bad (insert i S) ω = (¬ bad i ω ∧ avoidEvents bad S ω)
    from propext (avoidEvents_insert bad S i ω)]
  by_cases hb : bad i ω <;> by_cases hg : avoidEvents bad S ω <;> simp [hb, hg]

theorem eventProb_avoid_difference_mono (bad : I → Ω → Prop)
    (i : I) (S T : Finset I) (hTS : T ⊆ S) :
    eventProb (avoidEvents bad S) - eventProb (avoidEvents bad (insert i S)) ≤
      eventProb (avoidEvents bad T) - eventProb (avoidEvents bad (insert i T)) := by
  rw [eventProb_avoid_difference, eventProb_avoid_difference]
  apply eventProb_mono
  rintro ω ⟨hbad, hgood⟩
  exact ⟨hbad, fun j hj => hgood j (hTS hj)⟩

/-- The asymmetric Lovász Local Lemma on a finite uniform sample space.

The only probabilistic hypothesis is independence of a bad event from the
joint avoidance of each subfamily of its non-neighbours.  The probability
lower bound is proved, not supplied as a hypothesis.
-/
theorem eventProb_local_lemma [Nonempty Ω] (edges : Finset I) (bad : I → Ω → Prop)
    (x : I → ℝ) (N : I → Finset I)
    (hN : ∀ i ∈ edges, N i ⊆ edges)
    (hx0 : ∀ i ∈ edges, 0 ≤ x i) (hx1 : ∀ i ∈ edges, x i ≤ 1)
    (hbound : ∀ i ∈ edges,
      eventProb (bad i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hindep : ∀ i ∈ edges, ∀ S ⊆ edges, i ∉ S → Disjoint S (N i) →
      eventProb (fun ω => bad i ω ∧ avoidEvents bad S ω) =
        eventProb (bad i) * eventProb (avoidEvents bad S)) :
    (∏ i ∈ edges, (1 - x i)) ≤ eventProb (avoidEvents bad edges) := by
  apply finite_local_lemma edges (fun S => eventProb (avoidEvents bad S))
    (fun i => eventProb (bad i)) x N
  · simp [avoidEvents, eventProb]
  · exact fun S => eventProb_nonneg _
  · exact eventProb_avoid_difference_mono bad
  · exact hN
  · exact hx0
  · exact hx1
  · exact hbound
  · intro i hi S hS hiS hdis
    rw [eventProb_avoid_difference, hindep i hi S hS hiS hdis]

/-- Claim 2.4, with the support-based dependency condition as an explicit input.

The manuscript's independent-coordinate sampling supplies `hindep`; this
theorem proves all remaining probability and weight estimates, including the
finite local lemma and the precise `(1-1/(2r))^m` lower bound.
-/
theorem small_load_completion_of_dependency [Nonempty Ω]
    (edges : Finset I) (support : I → Finset V) (bad : I → Ω → Prop)
    (r : ℝ) (hr : 1 ≤ r) (m : ℕ) (hm : edges.card ≤ m)
    (hload : ∀ v,
      vertexLoad edges support (fun i => eventProb (bad i)) v < 1 / (4 * r))
    (hne : ∀ i ∈ edges, (support i).Nonempty)
    (hcard : ∀ i ∈ edges, ((support i).card : ℝ) ≤ r)
    (hindep : ∀ i ∈ edges, ∀ S ⊆ edges, i ∉ S →
      Disjoint S (neighbors edges support i) →
      eventProb (fun ω => bad i ω ∧ avoidEvents bad S ω) =
        eventProb (bad i) * eventProb (avoidEvents bad S)) :
    (1 - 1 / (2 * r)) ^ m ≤ eventProb (avoidEvents bad edges) := by
  let p : I → ℝ := fun i => eventProb (bad i)
  have hp : ∀ i ∈ edges, 0 ≤ p i := fun i hi => eventProb_nonneg _
  have hx := fun (i : I) (hi : i ∈ edges) =>
    doubled_weights_satisfy_lll edges support p r hr hp hload hne hcard hi
  have hLLL := eventProb_local_lemma edges bad (fun i => 2 * p i)
    (neighbors edges support) (fun i hi => neighbors_subset edges support i)
    (fun i hi => (hx i hi).1) (fun i hi => (hx i hi).2.1.le)
    (fun i hi => (hx i hi).2.2) hindep
  exact (completion_product_lower_bound edges support p r hr m hm hp hload hne).trans hLLL

end FiniteProbability

end ImprovedSidorenko.LocalLemma
