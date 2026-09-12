import DerridaRetaux.Main.ContinuumLaplaceGap
import DerridaRetaux.Main.ContinuumThirdTail
import DerridaRetaux.Analysis.HalfLineDensityMeasure
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

def subsequentialThirdRemainder
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t p : ℝ) : ℝ :=
  integratedExpThirdRemainder
    (halfLineDensityMeasure (fun x ↦ gluedExhaustionLimit g t x)) p

/-- Exact third-order Taylor decomposition of the continuum Laplace gap. -/
theorem subsequentialLaplaceGap_taylor
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    subsequentialLaplaceGap g t p =
      (p ^ 2 / 2) * continuumMoment
          (fun x ↦ gluedExhaustionLimit g t x) 2 -
        (p ^ 3 / 6) * continuumMoment
          (fun x ↦ gluedExhaustionLimit g t x) 3 +
        subsequentialThirdRemainder g t p := by
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hucont := subsequential_slice_continuous_for_gap m data phi g hlim ht
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hi : ∀ r : ℕ, r ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0) := by
    intro r hr
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht r hr
  let μ := halfLineDensityMeasure u
  have hiμ : ∀ r : ℕ, r ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ r) (Ici 0) μ := by
    intro r hr
    rw [integrableOn_halfLineDensityMeasure_iff u (fun x : ℝ ↦ x ^ r)
      hucont hunonneg]
    exact hi r hr
  have hTaylor := integratedLaplaceSecondGap_eq μ hp
    (hiμ 2 (by norm_num)) (hiμ 3 (by norm_num))
  rw [← subsequentialLaplaceGap_eq_integrated
      m data phi g hphi hlim ht hp,
    positiveHalfLineMoment_halfLineDensityMeasure u 2 hucont hunonneg,
    positiveHalfLineMoment_halfLineDensityMeasure u 3 hucont hunonneg]
    at hTaylor
  simpa only [u, μ, subsequentialThirdRemainder] using hTaylor

/-- Quantitative source remainder estimate, uniform up to a constant depending
on the subsequential limit data and the fixed Laplace parameter. -/
theorem subsequentialThirdRemainder_normalized_le_sqrt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      |subsequentialThirdRemainder g t p /
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3| ≤
          K * Real.sqrt t := by
  obtain ⟨c, C, hc, hC, hb⟩ :=
    subsequentialMoment_rigidityBounds m data phi g hphi hlim
  obtain ⟨D, hD, htail⟩ :=
    subsequentialThirdMomentTail m data phi g hphi hlim
  let K : ℝ := p ^ 4 / 24 + p ^ 3 * D / (6 * c)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro t ht
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hucont := subsequential_slice_continuous_for_gap m data phi g hlim ht
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0) := by
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht 3 (by norm_num)
  let μ := halfLineDensityMeasure u
  have hthirdμ : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ := by
    rw [integrableOn_halfLineDensityMeasure_iff u (fun x : ℝ ↦ x ^ 3)
      hucont hunonneg]
    exact hthird
  have htailμ : positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
      D * t ^ 3 / Real.sqrt t := by
    rw [positiveHalfLineThirdMomentTail_halfLineDensityMeasure u
      (Real.sqrt t) (Real.sqrt_nonneg t) hucont hunonneg]
    simpa only [u] using htail t (Real.sqrt t) ht (Real.sqrt_pos.2 ht)
  have hbound := abs_normalizedIntegratedExpThirdRemainder_le_sqrt
    μ hp ht hc hD.le hthirdμ (by
      rw [positiveHalfLineMoment_halfLineDensityMeasure u 3 hucont hunonneg]
      simpa only [u] using (hb t ht).1) htailμ
  simpa only [K, μ, u, subsequentialThirdRemainder,
    positiveHalfLineMoment_halfLineDensityMeasure u 3 hucont hunonneg] using hbound

/-- The normalized third-order remainder vanishes at the entrance. -/
theorem subsequentialThirdRemainder_normalized_tendsto_zero
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto
      (fun t : ℝ ↦ subsequentialThirdRemainder g t p /
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ :=
    subsequentialThirdRemainder_normalized_le_sqrt
      m data phi g hphi hlim p hp
  have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).mono_left inf_le_left
  have hupper : Tendsto (fun t : ℝ ↦ K * Real.sqrt t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert tendsto_const_nhds.mul hsqrt using 1 <;> ring
  obtain ⟨c, C, hc, hC, hrigid⟩ :=
    subsequentialMoment_rigidityBounds m data phi g hphi hlim
  apply squeeze_zero' _ _ hupper
  · filter_upwards [self_mem_nhdsWithin] with t ht
    unfold subsequentialThirdRemainder
    exact div_nonneg
      (integratedExpThirdRemainder_nonneg _ hp)
      ((mul_pos hc (sq_pos_of_pos ht)).trans_le (hrigid t ht).1).le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (le_abs_self _).trans (hbound t ht)

end

end DerridaRetaux.FixedArity
