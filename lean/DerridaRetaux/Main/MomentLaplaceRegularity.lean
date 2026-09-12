import DerridaRetaux.Main.MomentLaplaceODE
import DerridaRetaux.Analysis.LocalACClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Continuous derivatives give the full integral representation on a compact interval. -/
theorem hasIntegralDerivativeOn_of_continuous_derivative
    (F v : ℝ → ℝ) (a b : ℝ)
    (hv : ContinuousOn v (Icc a b))
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (v t) t) :
    HasIntegralDerivativeOn F v (Icc a b) := by
  refine ⟨hv.integrableOn_Icc, ?_⟩
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hrepr := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hF t (hsub (by simpa [uIcc_of_le hxy] using ht)))
    (ContinuousOn.intervalIntegrable_of_Icc hxy (hv.mono hsub))
  rw [Measure.restrict_restrict_of_subset (Ioc_subset_Icc_self.trans hsub)]
  rw [← intervalIntegral.integral_of_le hxy]
  exact hrepr.symm

namespace FixedArity

/-- The local absolute continuity clause of `lem:momentODE`, expressed by an integrable
derivative and the fundamental theorem on every subinterval of every positive compact
time interval. These are the actual moments and Laplace transforms of the limit. -/
theorem momentLaplaceLocalIntegralDerivatives
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop) :
    let A : ℕ → ℝ → ℝ := fun r t ↦
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
    let U : ℝ → ℝ → ℝ := fun t p ↦
      continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p
    let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
    ∀ a b : ℝ, 0 < a → a ≤ b →
      HasIntegralDerivativeOn (A 0)
        (fun t ↦ -beta t + (1 / 2 : ℝ) * A 0 t ^ 2) (Icc a b) ∧
      HasIntegralDerivativeOn (A 2)
        (fun t ↦ A 0 t * A 2 t - 1) (Icc a b) ∧
      HasIntegralDerivativeOn (A 3)
        (fun t ↦ A 0 t * A 3 t) (Icc a b) ∧
      ∀ p : ℝ, 0 ≤ p → HasIntegralDerivativeOn (fun t ↦ U t p)
        (fun t ↦ p * U t p + (1 / 2 : ℝ) * U t p ^ 2 - beta t) (Icc a b) := by
  dsimp only
  intro a b ha hab
  let A : ℕ → ℝ → ℝ := fun r t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
  let U : ℝ → ℝ → ℝ := fun t p ↦
    continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p
  let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
  have hode := momentLaplaceODE m data phi g hphi hlim
  have hA : ∀ r : ℕ, r ≤ 3 → ContinuousOn (A r) (Icc a b) := by
    intro r hr
    exact subsequentialMoment_continuousOn m data phi g hphi hlim r hr a b ha hab
  have hbeta : ContinuousOn beta (Icc a b) := by
    have hbox := continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim a b 0 ha hab le_rfl
    change ContinuousOn
      ((fun q : ℝ × ℝ ↦ gluedExhaustionLimit g q.1 q.2) ∘ (fun t : ℝ ↦ (t, 0)))
      (Icc a b)
    exact hbox.comp (by fun_prop) (fun t ht ↦ ⟨ht, le_rfl, le_rfl⟩)
  refine ⟨hasIntegralDerivativeOn_of_continuous_derivative _ _ a b
      (hbeta.neg.add (continuousOn_const.mul ((hA 0 (by norm_num)).pow 2)))
      (fun t ht ↦ hode.1 t (ha.trans_le ht.1)),
    hasIntegralDerivativeOn_of_continuous_derivative _ _ a b
      (((hA 0 (by norm_num)).mul (hA 2 (by norm_num))).sub continuousOn_const)
      (fun t ht ↦ hode.2.1 t (ha.trans_le ht.1)),
    hasIntegralDerivativeOn_of_continuous_derivative _ _ a b
      ((hA 0 (by norm_num)).mul (hA 3 (by norm_num)))
      (fun t ht ↦ hode.2.2.1 t (ha.trans_le ht.1)), ?_⟩
  intro p hp
  have hU : ContinuousOn (fun t ↦ U t p) (Icc a b) :=
    subsequentialLaplace_continuousOn m data phi g hphi hlim p hp a b ha hab
  exact hasIntegralDerivativeOn_of_continuous_derivative _ _ a b
    (((continuousOn_const.mul hU).add (continuousOn_const.mul (hU.pow 2))).sub hbeta)
    (fun t ht ↦ hode.2.2.2 p hp t (ha.trans_le ht.1))

end FixedArity
end
end DerridaRetaux
