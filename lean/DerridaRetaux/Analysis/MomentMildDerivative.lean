import DerridaRetaux.Analysis.HalfLineShiftLaplace
import DerridaRetaux.Analysis.ShrinkingIntervalDerivative
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Abstract right-derivative closure for a moment of a mild solution.  The
spatial Fubini step is represented by the exact displayed identity `hmild`; the
shrinking time interval then contributes its endpoint integrand. -/
theorem hasDerivWithinAt_moment_of_mildIdentity
    (u : ℝ → ℝ → ℝ) (r : ℕ) (t transportDerivative : ℝ)
    (hmild : ∀ h : ℝ, 0 ≤ h →
      continuumMoment (u (t + h)) r =
        shiftedHalfLineMoment (u t) r h +
          ∫ s in t..t + h, (1 / 2 : ℝ) *
            shiftedHalfLineMoment (positiveSelfConvolution (u s)) r
              (t + h - s))
    (htransport : HasDerivWithinAt (shiftedHalfLineMoment (u t) r)
      transportDerivative (Ici 0) 0)
    (hG : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) *
        shiftedHalfLineMoment (positiveSelfConvolution (u z.2)) r
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t))
    (hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable
      (fun s ↦ (1 / 2 : ℝ) *
        shiftedHalfLineMoment (positiveSelfConvolution (u s)) r
          (t + h - s)) volume t (t + h)) :
    HasDerivWithinAt (fun h ↦ continuumMoment (u (t + h)) r)
      (transportDerivative +
        (1 / 2 : ℝ) * continuumMoment (positiveSelfConvolution (u t)) r)
      (Ici 0) 0 := by
  let G : ℝ → ℝ → ℝ := fun h s ↦ (1 / 2 : ℝ) *
    shiftedHalfLineMoment (positiveSelfConvolution (u s)) r (t + h - s)
  have hshrink := hasDerivWithinAt_shrinkingInterval G t hG hInt
  have hsum := htransport.add hshrink
  have hGzero : G 0 t =
      (1 / 2 : ℝ) * continuumMoment (positiveSelfConvolution (u t)) r := by
    simp [G, shiftedHalfLineMoment, continuumMoment]
  rw [hGzero] at hsum
  apply hsum.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact hmild h hh
  · simp [G, shiftedHalfLineMoment, continuumMoment]

end

end DerridaRetaux
