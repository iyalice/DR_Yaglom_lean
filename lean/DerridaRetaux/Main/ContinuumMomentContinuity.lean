import DerridaRetaux.Main.ContinuumThirdTail
import DerridaRetaux.Analysis.GluedCompactBox
import DerridaRetaux.Analysis.MomentTailMonotonicity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- All continuum moments of order at most three vary continuously on every
compact positive-time interval.  The third-tail source estimate supplies the
uniform integrability missing from local uniform convergence alone. -/
theorem subsequentialMoment_continuousOn
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (r : ℕ) (hr : r ≤ 3) (eta T : ℝ)
    (heta : 0 < eta) (hetaT : eta ≤ T) :
    ContinuousOn
      (fun t : ℝ ↦ continuumMoment
        (fun x ↦ gluedExhaustionLimit g t x) r) (Icc eta T) := by
  let u : ℝ → ℝ → ℝ := fun t x ↦ gluedExhaustionLimit g t x
  have hT : 0 < T := heta.trans_le hetaT
  have hu : ∀ R : ℝ, 0 ≤ R →
      ContinuousOn (Function.uncurry u)
        (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
    intro R hR
    simpa only [u] using
      continuousOn_gluedExhaustionLimit_compactBox
        (orbitScaledGrid m data.law) phi g hlim eta T R heta hetaT hR
  have hnonneg : ∀ t x : ℝ, t ∈ Icc eta T → 0 ≤ x → 0 ≤ u t x := by
    intro t x ht hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim (heta.trans_le ht.1) hx
  have hint : ∀ t : ℝ, t ∈ Icc eta T →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u t x) (Ici 0) := by
    intro t ht
    simpa only [u] using
      subsequentialMoment_integrable
        m data.law data.arity data.critical data.third
          data.notBinaryFixedPoint phi g hphi hlim t
            (heta.trans_le ht.1) r hr
  obtain ⟨C, hC, hthirdTail⟩ :=
    subsequentialThirdMomentTail m data phi g hphi hlim
  have htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ R : ℕ in atTop, ∀ t : ℝ, t ∈ Icc eta T →
        (∫ x in Ioi (R : ℝ), x ^ r * u t x) < epsilon := by
    intro epsilon hepsilon
    have hzero := tendsto_const_div_atTop_nhds_zero_nat (C * T ^ 3)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hzero epsilon hepsilon
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with R hRN hR1
    intro t ht
    have htpos : 0 < t := heta.trans_le ht.1
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR1)
    have hintr := hint t ht
    have hint3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u t x) (Ici 0) := by
      simpa only [u] using
        subsequentialMoment_integrable
          m data.law data.arity data.critical data.third
            data.notBinaryFixedPoint phi g hphi hlim t htpos 3 (by norm_num)
    have hlower := lowerMomentTail_le_thirdMomentTail (u t) r (R : ℝ)
      hr (by exact_mod_cast hR1) (fun x hx ↦ hnonneg t x ht hx) hintr hint3
    have hthird := hthirdTail t (R : ℝ) htpos hRpos
    have htime : C * t ^ 3 / (R : ℝ) ≤ C * T ^ 3 / (R : ℝ) := by
      gcongr
      exact ht.2
    have hnear := hN R hRN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (mul_nonneg hC.le (pow_nonneg hT.le 3))
        (Nat.cast_nonneg R))] at hnear
    exact lt_of_le_of_lt (hlower.trans (hthird.trans htime)) hnear
  simpa only [u] using
    continuousOn_continuumMoment_of_uniformTails u r eta T hu hnonneg hint htail

end

end DerridaRetaux.FixedArity
