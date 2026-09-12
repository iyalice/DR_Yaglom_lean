import DerridaRetaux.Main.ContinuumMomentContinuity
import DerridaRetaux.Analysis.PositiveConvolutionMomentIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The positive self-convolution of a continuum slice has every moment up
to order three integrable. -/
theorem subsequentialConvolutionMoment_integrable
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) (r : ℕ) (hr : r ≤ 3) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ r * positiveSelfConvolution
        (fun y ↦ gluedExhaustionLimit g t y) x) (Ici 0) := by
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible
      (fun N q ↦ gridBilinearInterp N (orbitScaledGrid m data.law N) q.1 q.2)
      phi g hlim hkl p
  have hucont : ContinuousOn u (Ici (0 : ℝ)) :=
    continuousOn_gluedExhaustionLimit_timeSlice_Ici g hcompat t ht
  apply integrableOn_pow_mul_positiveSelfConvolution u r hucont
  intro k hk
  simpa only [u] using
    subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht k (hk.trans hr)

/-- Convolution moments up to order three are continuous on compact
positive-time intervals. -/
theorem subsequentialConvolutionMoment_continuousOn
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
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) r)
      (Icc eta T) := by
  let u : ℝ → ℝ → ℝ := fun t x ↦ gluedExhaustionLimit g t x
  let A : ℕ → ℝ → ℝ := fun k t ↦ continuumMoment (u t) k
  let B : ℝ → ℝ := fun t ↦
    ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * A k t * A (r - k) t
  have hA : ∀ k : ℕ, k ≤ r → ContinuousOn (A k) (Icc eta T) := by
    intro k hk
    simpa only [A, u] using
      subsequentialMoment_continuousOn m data phi g hphi hlim k
        (hk.trans hr) eta T heta hetaT
  have hB : ContinuousOn B (Icc eta T) := by
    dsimp only [B]
    apply continuousOn_finset_sum
    intro k hk
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (continuousOn_const.mul (hA k hkr)).mul
      (hA (r - k) (Nat.sub_le r k))
  apply hB.congr
  intro t htmem
  let slice : ℝ → ℝ := u t
  have ht : 0 < t := heta.trans_le htmem.1
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible
      (fun N q ↦ gridBilinearInterp N (orbitScaledGrid m data.law N) q.1 q.2)
      phi g hlim hkl p
  have hscont : ContinuousOn slice (Ici (0 : ℝ)) :=
    continuousOn_gluedExhaustionLimit_timeSlice_Ici g hcompat t ht
  have hsmom : ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * slice x) (Ici 0) := by
    intro k hk
    simpa only [slice, u] using
      subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim t ht k (hk.trans hr)
  simpa only [B, A, u, slice] using
    (continuumMoment_positiveSelfConvolution slice r hscont hsmom)

end

end DerridaRetaux.FixedArity
