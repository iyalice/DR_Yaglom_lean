import DerridaRetaux.Main.ContinuumShiftedConvolutionTriangle
import DerridaRetaux.Main.ContinuumPositiveHalfStrip
import DerridaRetaux.Analysis.MomentDuhamelIntegrability
import DerridaRetaux.Analysis.PositiveConvolutionNonneg
import DerridaRetaux.Analysis.ShiftedMomentIntegrability
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequentialConvolution_nonneg
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    0 ≤ positiveSelfConvolution
      (fun y ↦ gluedExhaustionLimit g s y) x := by
  exact positiveSelfConvolution_nonneg
    (fun y ↦ gluedExhaustionLimit g s y)
    (fun y hy ↦ gluedExhaustionLimit_nonneg m data.law data.arity
      data.critical phi g hphi hlim hs hy) hx

theorem subsequentialShiftedConvolutionMoment_integrableOn
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t h s : ℝ) (ht : 0 < t) (hh : 0 ≤ h)
    (hslo : t ≤ s) (hshi : s ≤ t + h)
    (r : ℕ) (hr : r ≤ 3) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ r * positiveSelfConvolution
        (fun y ↦ gluedExhaustionLimit g s y) (x + (t + h - s)))
      (Ici 0) := by
  let v : ℝ → ℝ → ℝ := fun q ↦
    positiveSelfConvolution (fun y ↦ gluedExhaustionLimit g q y)
  have hvFull : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [v] using
      subsequentialConvolution_continuousOn_positiveHalfStrip
        m data phi g hlim t ht
  have hvcont : ContinuousOn (v s) (Ici (0 : ℝ)) := by
    let emb : ℝ → ℝ × ℝ := fun x ↦ (s, x)
    change ContinuousOn ((Function.uncurry v) ∘ emb) (Ici (0 : ℝ))
    exact hvFull.comp (by dsimp only [emb]; fun_prop)
      (fun x hx ↦ ⟨hslo, hx⟩)
  have hvnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ v s x := by
    intro x hx
    simpa only [v] using
      subsequentialConvolution_nonneg m data phi g hphi hlim
        (ht.trans_le hslo) hx
  have hvmom : IntegrableOn (fun x : ℝ ↦ x ^ r * v s x) (Ici 0) := by
    simpa only [v] using
      subsequentialConvolutionMoment_integrable
        m data phi g hphi hlim s (ht.trans_le hslo) r hr
  simpa only [v] using integrableOn_shifted_pow_mul
    (v s) r (t + h - s) (by linarith) hvcont hvnonneg hvmom

theorem subsequentialShiftedConvolutionMoment_integrableOn_time
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t h : ℝ) (ht : 0 < t) (hh : 0 ≤ h)
    (r : ℕ) (hr : r ≤ 3) :
    IntegrableOn
      (fun s : ℝ ↦ (1 / 2 : ℝ) * shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)) r
          (t + h - s)) (Ioc t (t + h)) := by
  have htri := subsequentialShiftedConvolutionMoment_continuousOn_triangle
    m data phi g hphi hlim t h ht hh r hr
  have hshiftCont : ContinuousOn
      (fun s : ℝ ↦ shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)) r
          (t + h - s)) (Icc t (t + h)) := by
    let emb : ℝ → ℝ × ℝ := fun s ↦ (h, s)
    change ContinuousOn ((fun z : ℝ × ℝ ↦ shiftedHalfLineMoment
      (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) r
        (t + z.1 - z.2)) ∘ emb) (Icc t (t + h))
    exact htri.comp (by dsimp only [emb]; fun_prop)
      (fun s hs ↦ by
        dsimp only [emb]
        exact ⟨hh, le_rfl, hs.1, by simpa using hs.2⟩)
  exact ((continuousOn_const.mul hshiftCont).integrableOn_compact
    isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- The polynomially weighted Duhamel kernel is integrable in space-time on
every finite forward interval.  This discharges the Fubini premise used to
pass from the pointwise mild equation to moment identities. -/
theorem subsequentialMomentDuhamelIntegrable
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t h : ℝ) (ht : 0 < t) (hh : 0 ≤ h)
    (r : ℕ) (hr : r ≤ 3) :
    Integrable
      (momentDuhamelIntegrand
        (fun s x ↦ gluedExhaustionLimit g s x) r t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
  let v : ℝ → ℝ → ℝ := fun s ↦
    positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)
  have hvcont : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [v] using
      subsequentialConvolution_continuousOn_positiveHalfStrip
        m data phi g hlim t ht
  have hvnonneg : ∀ s x : ℝ, t ≤ s → 0 ≤ x → 0 ≤ v s x := by
    intro s x hs hx
    simpa only [v] using
      subsequentialConvolution_nonneg m data phi g hphi hlim
        (ht.trans_le hs) hx
  have hslice : ∀ s : ℝ, s ∈ Ioc t (t + h) →
      IntegrableOn (fun x : ℝ ↦ x ^ r * v s (x + (t + h - s)))
        (Ici 0) := by
    intro s hs
    simpa only [v] using
      subsequentialShiftedConvolutionMoment_integrableOn
        m data phi g hphi hlim t h s ht hh hs.1.le hs.2 r hr
  have hshift : IntegrableOn
      (fun s : ℝ ↦ (1 / 2 : ℝ) *
        shiftedHalfLineMoment (v s) r (t + h - s))
      (Ioc t (t + h)) := by
    simpa only [v] using
      subsequentialShiftedConvolutionMoment_integrableOn_time
        m data phi g hphi hlim t h ht hh r hr
  have hgeneric := integrable_weightedShiftedKernel
    v r t h hh hvcont hvnonneg hslice hshift
  simpa only [weightedShiftedKernel, momentDuhamelIntegrand, v] using hgeneric

end

end DerridaRetaux.FixedArity
