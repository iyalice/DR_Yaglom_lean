import DerridaRetaux.Analysis.EventuallyLocalUniform
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- The epsilon/eventual formulation of uniform convergence on every finite
lattice window implies `LocallyUniformLatticeDensity`.  The maximum over the
finite set of nodes supplies the error modulus required by that definition. -/
theorem locallyUniformLatticeDensity_of_eventually_epsilon
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hlocal : ∀ R : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, 0 < scale n → ∀ j : ℕ,
        j ≤ R * scale n →
          |(scale n : ℝ) ^ 2 * rho n j -
            u ((j : ℝ) / (scale n : ℝ))| < ε) :
    LocallyUniformLatticeDensity rho scale u := by
  intro R
  let nodes : ℕ → Finset ℝ := fun n ↦
    (Finset.range (R * scale n + 1)).image fun j ↦
      |(scale n : ℝ) ^ 2 * rho n j -
        u ((j : ℝ) / (scale n : ℝ))|
  have hnodes : ∀ n, (nodes n).Nonempty := by
    intro n
    refine ⟨|(scale n : ℝ) ^ 2 * rho n 0 - u 0|, ?_⟩
    simp only [nodes, Finset.mem_image, Finset.mem_range]
    refine ⟨0, by omega, ?_⟩
    simp
  let error : ℕ → ℝ := fun n ↦
    if 0 < scale n then (nodes n).max' (hnodes n) else 0
  have herrorNonneg : ∀ n, 0 ≤ error n := by
    intro n
    by_cases hn : 0 < scale n
    · simp only [error, if_pos hn]
      exact (abs_nonneg _).trans
        (Finset.le_max' (nodes n)
          |(scale n : ℝ) ^ 2 * rho n 0 - u 0| (by
            simp only [nodes, Finset.mem_image, Finset.mem_range]
            refine ⟨0, by omega, ?_⟩
            simp))
    · simp [error, hn]
  have herror : Tendsto error atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hlocal R ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (herrorNonneg n)]
    by_cases hscale : 0 < scale n
    · simp only [error, if_pos hscale]
      apply (Finset.max'_lt_iff (nodes n) (hnodes n)).2
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact hn hscale j (by
        rw [Finset.mem_range] at hj
        omega)
    · simp [error, hscale, hε]
  refine ⟨error, herror, ?_⟩
  intro n hn j hj
  simp only [error, if_pos hn]
  apply Finset.le_max' (nodes n)
  rw [Finset.mem_image]
  refine ⟨j, ?_, rfl⟩
  rw [Finset.mem_range]
  omega

end

end DerridaRetaux
