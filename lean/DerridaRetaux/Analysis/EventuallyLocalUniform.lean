import DerridaRetaux.Analysis.LatticeRiemannLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- An eventual local-uniform lattice estimate can absorb its finite exceptional
prefix into the error modulus.  This is the bookkeeping bridge between the
eventual estimates naturally produced by compact convergence and the all-index
form of `LocallyUniformLatticeDensity`. -/
theorem locallyUniformLatticeDensity_of_eventually
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hlocal : ∀ R : ℕ, ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < scale n → ∀ j : ℕ,
          j ≤ R * scale n →
            |(scale n : ℝ) ^ 2 * rho n j -
              u ((j : ℝ) / (scale n : ℝ))| ≤ error n) :
    LocallyUniformLatticeDensity rho scale u := by
  intro R
  obtain ⟨error, herror, hevent⟩ := hlocal R
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let prefixError : ℕ → ℝ := fun n ↦
    ∑ j ∈ Finset.range (R * scale n + 1),
      |(scale n : ℝ) ^ 2 * rho n j -
        u ((j : ℝ) / (scale n : ℝ))|
  let totalError : ℕ → ℝ := fun n ↦
    if n < N then prefixError n else max (error n) 0
  have htotal : Tendsto totalError atTop (nhds 0) := by
    have hmax : Tendsto (fun n ↦ max (error n) 0) atTop (nhds 0) := by
      simpa using herror.max (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
    apply hmax.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [totalError, if_neg (not_lt.mpr hn)]
  refine ⟨totalError, htotal, ?_⟩
  intro n hn j hj
  by_cases hnN : n < N
  · simp only [totalError, if_pos hnN]
    have hjmem : j ∈ Finset.range (R * scale n + 1) := by
      rw [Finset.mem_range]
      omega
    exact Finset.single_le_sum
      (fun i _ ↦ abs_nonneg
        ((scale n : ℝ) ^ 2 * rho n i -
          u ((i : ℝ) / (scale n : ℝ)))) hjmem
  · simp only [totalError, if_neg hnN]
    exact (hN n (not_lt.mp hnN) hn j hj).trans (le_max_left _ _)

end

end DerridaRetaux
