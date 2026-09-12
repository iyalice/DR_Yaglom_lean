import DerridaRetaux.Main.ContinuumConvolutionMoments
import DerridaRetaux.Analysis.ShiftedMomentContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

private theorem subsequentialConvolution_continuousOn_unitBox
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ positiveSelfConvolution
        (fun x ↦ gluedExhaustionLimit g p.1 x) p.2)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have hu : ContinuousOn (Function.uncurry u)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [u] using
      continuousOn_gluedExhaustionLimit_compactBox
        (orbitScaledGrid m data.law) phi g hlim (t / 2) (t + 1) 1
          (half_pos ht) (by linarith) (by norm_num)
  simpa only [u] using continuousOn_positiveSelfConvolution_uncurry
    u (t / 2) (t + 1) 1 (by linarith) (by norm_num) hu

/-- The shifted convolution mass is continuous at the collapsed Duhamel
endpoint along the forward integration triangle. -/
theorem subsequentialShiftedConvolution_zero_continuousWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) 0
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [v, u] using
      subsequentialConvolution_continuousOn_unitBox m data phi g hlim t ht
  have hB0 : ContinuousOn (fun s : ℝ ↦ continuumMoment (v s) 0)
      (Icc t (t + 1)) := by
    simpa only [v, u] using
      subsequentialConvolutionMoment_continuousOn m data phi g hphi hlim
        0 (by norm_num) t (t + 1) ht (by linarith)
  have hint0 : ∀ s : ℝ, t ≤ s → IntegrableOn (v s) (Ici 0) := by
    intro s hs
    have hspos : 0 < s := ht.trans_le hs
    simpa only [v, u, pow_zero, one_mul] using
      subsequentialConvolutionMoment_integrable m data phi g hphi hlim
        s hspos 0 (by norm_num)
  simpa only [v, u] using
    continuousWithinAt_shiftedHalfLineMoment_zero v t ht hv hB0 hint0

/-- The shifted second convolution moment is continuous at the collapsed
Duhamel endpoint along the forward integration triangle. -/
theorem subsequentialShiftedConvolution_two_continuousWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) 2
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [v, u] using
      subsequentialConvolution_continuousOn_unitBox m data phi g hlim t ht
  have hB : ∀ k : ℕ, k ≤ 2 → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + 1)) := by
    intro k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_continuousOn m data phi g hphi hlim
        k (hk.trans (by norm_num)) t (t + 1) ht (by linarith)
  have hint : ∀ s : ℝ, t ≤ s → ∀ k : ℕ, k ≤ 2 →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0) := by
    intro s hs k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_integrable m data phi g hphi hlim
        s (ht.trans_le hs) k (hk.trans (by norm_num))
  simpa only [v, u] using
    continuousWithinAt_shiftedHalfLineMoment_two v t ht hv hB hint

/-- The shifted third convolution moment is continuous at the collapsed
Duhamel endpoint along the forward integration triangle. -/
theorem subsequentialShiftedConvolution_three_continuousWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) 3
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [v, u] using
      subsequentialConvolution_continuousOn_unitBox m data phi g hlim t ht
  have hB : ∀ k : ℕ, k ≤ 3 → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + 1)) := by
    intro k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_continuousOn m data phi g hphi hlim
        k hk t (t + 1) ht (by linarith)
  have hint : ∀ s : ℝ, t ≤ s → ∀ k : ℕ, k ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0) := by
    intro s hs k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_integrable m data phi g hphi hlim
        s (ht.trans_le hs) k hk
  simpa only [v, u] using
    continuousWithinAt_shiftedHalfLineMoment_three v t ht hv hB hint

end

end DerridaRetaux.FixedArity
