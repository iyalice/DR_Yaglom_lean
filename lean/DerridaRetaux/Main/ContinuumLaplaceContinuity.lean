import DerridaRetaux.Main.ContinuumMomentContinuity
import DerridaRetaux.Main.ContinuumPositiveHalfStrip
import DerridaRetaux.Analysis.ContinuumLaplaceContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Every nonnegative-parameter Laplace transform of a glued subsequential
limit is continuous on compact positive-time intervals. -/
theorem subsequentialLaplace_continuousOn
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) (eta T : ℝ)
    (heta : 0 < eta) (hetaT : eta ≤ T) :
    ContinuousOn
      (fun t : ℝ ↦ continuumLaplace
        (fun x ↦ gluedExhaustionLimit g t x) p) (Icc eta T) := by
  let u : ℝ → ℝ → ℝ := fun t x ↦ gluedExhaustionLimit g t x
  have hT : 0 < T := heta.trans_le hetaT
  have hu : ∀ R : ℝ, 0 ≤ R → ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
    intro R hR
    simpa only [u] using continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim eta T R heta hetaT hR
  have hnonneg : ∀ t x : ℝ, t ∈ Icc eta T → 0 ≤ x → 0 ≤ u t x := by
    intro t x ht hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim (heta.trans_le ht.1) hx
  have h0 : ∀ t : ℝ, t ∈ Icc eta T → IntegrableOn (u t) (Ici 0) := by
    intro t ht
    simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t (heta.trans_le ht.1) 0 (by norm_num)
  have hLap : ∀ t : ℝ, t ∈ Icc eta T → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u t x) (Ici 0) := by
    intro t ht
    have huSlice : ContinuousOn (u t) (Ici (0 : ℝ)) := by
      have hfull := subsequentialDensity_continuousOn_positiveHalfStrip
        m data phi g hlim eta heta
      let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
      change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
      exact hfull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
        dsimp only [emb]
        change eta ≤ t ∧ (0 : ℝ) ≤ x
        exact ⟨ht.1, hx⟩)
    exact integrableOn_exp_neg_mul (u t) p hp huSlice
      (fun x hx ↦ hnonneg t x ht hx) (h0 t ht)
  obtain ⟨C, hC, hthirdTail⟩ :=
    subsequentialThirdMomentTail m data phi g hphi hlim
  have htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ R : ℕ in atTop, ∀ t : ℝ, t ∈ Icc eta T →
        (∫ x in Ioi (R : ℝ), u t x) < epsilon := by
    intro epsilon hepsilon
    have hz := tendsto_const_div_atTop_nhds_zero_nat (C * T ^ 3)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz epsilon hepsilon
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with R hRN hR1
    intro t ht
    have htpos : 0 < t := heta.trans_le ht.1
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR1)
    have hint3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u t x) (Ici 0) := by
      simpa only [u] using subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim t htpos 3 (by norm_num)
    have hlower := lowerMomentTail_le_thirdMomentTail (u t) 0 (R : ℝ)
      (by norm_num) (by exact_mod_cast hR1)
      (fun x hx ↦ hnonneg t x ht hx) (by simpa using h0 t ht) hint3
    have hthird := hthirdTail t (R : ℝ) htpos hRpos
    have htime : C * t ^ 3 / (R : ℝ) ≤ C * T ^ 3 / (R : ℝ) := by
      gcongr
      exact ht.2
    have hnear := hN R hRN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (mul_nonneg hC.le (pow_nonneg hT.le 3))
        (Nat.cast_nonneg R))] at hnear
    simpa only [pow_zero, one_mul] using
      lt_of_le_of_lt (hlower.trans (hthird.trans htime)) hnear
  simpa only [u] using continuousOn_continuumLaplace_of_uniformMassTails
    u p eta T hp hu hnonneg h0 hLap htail

end

end DerridaRetaux.FixedArity
