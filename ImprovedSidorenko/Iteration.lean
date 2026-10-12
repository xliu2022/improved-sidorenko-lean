module

public import Mathlib.Tactic

@[expose] public section

/-!
# Finite termination of the assignment stage

The rank is the number of unassigned vertices. A real-valued potential alone
does not justify termination; the natural-number rank decreases at each step.
This reusable theorem isolates that part of Claim 2.3.
-/

namespace ImprovedSidorenko

/-- A valid initial state and a rank-decreasing step give a valid terminal state. -/
theorem finite_descent {State : Type*} (rank : State → ℕ)
    (Valid Terminal : State → Prop)
    (step : ∀ s, Valid s → ¬ Terminal s →
      ∃ t, Valid t ∧ rank t < rank s)
    (s₀ : State) (h₀ : Valid s₀) : ∃ t, Valid t ∧ Terminal t := by
  have main : ∀ n, ∀ s, rank s = n → Valid s → ∃ t, Valid t ∧ Terminal t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hv
      by_cases ht : Terminal s
      · exact ⟨s, hv, ht⟩
      · obtain ⟨t, htv, hlt⟩ := step s hv ht
        exact ih (rank t) (by omega) t rfl htv
  exact main (rank s₀) s₀ rfl h₀

/-- Claim 2.3 after a concrete legal one-step choice has been established. -/
theorem small_load_state {State Vertex : Type*} (rank : State → ℕ)
    (Legal : State → Prop) (potential : State → ℝ)
    (unassigned : State → Vertex → Prop) (load : State → Vertex → ℝ)
    (M threshold : ℝ)
    (step : ∀ s, Legal s → potential s < M →
      (∃ v, unassigned s v ∧ threshold ≤ load s v) →
      ∃ t, Legal t ∧ potential t < potential s ∧ rank t < rank s)
    (s₀ : State) (hlegal : Legal s₀) (hpotential : potential s₀ < M) :
    ∃ t, Legal t ∧ potential t < M ∧
      ∀ v, unassigned t v → load t v < threshold := by
  classical
  have h := finite_descent rank
    (fun s => Legal s ∧ potential s < M)
    (fun s => ∀ v, unassigned s v → load s v < threshold)
    (by
      intro s hs hn
      change ¬ ∀ v, unassigned s v → load s v < threshold at hn
      push Not at hn
      obtain ⟨t, ht, hp, hr⟩ := step s hs.1 hs.2 hn
      exact ⟨t, ⟨ht, hp.trans hs.2⟩, hr⟩)
    s₀ ⟨hlegal, hpotential⟩
  obtain ⟨t, ⟨ht, hp⟩, hl⟩ := h
  exact ⟨t, ht, hp, hl⟩

end ImprovedSidorenko
