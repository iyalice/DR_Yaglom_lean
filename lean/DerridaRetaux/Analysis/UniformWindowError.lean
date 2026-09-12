import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- Convert an epsilon/eventual uniform estimate on moving finite windows into
an explicit all-index error modulus tending to zero. -/
theorem exists_tendsto_zero_error_of_eventuallyUniform_window
    (lo hi : ℕ → ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n), |F n s| < ε) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n : ℕ, ∀ s ∈ Finset.Ico (lo n) (hi n), |F n s| ≤ error n := by
  let values : ℕ → Finset ℝ := fun n ↦
    insert 0 ((Finset.Ico (lo n) (hi n)).image fun s ↦ |F n s|)
  have hvalues : ∀ n, (values n).Nonempty := fun n ↦ ⟨0, by simp [values]⟩
  let error : ℕ → ℝ := fun n ↦ (values n).max' (hvalues n)
  have herrorNonneg : ∀ n, 0 ≤ error n := by
    intro n
    exact Finset.le_max' (values n) 0 (by simp [values])
  have herror : Tendsto error atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hF ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (herrorNonneg n)]
    apply (Finset.max'_lt_iff (values n) (hvalues n)).2
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hε
    · rw [Finset.mem_image] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact hn s hs
  refine ⟨error, herror, ?_⟩
  intro n s hs
  apply Finset.le_max' (values n)
  simp only [values, Finset.mem_insert, Finset.mem_image]
  exact Or.inr ⟨s, hs, rfl⟩

end

end DerridaRetaux
