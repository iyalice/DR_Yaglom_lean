import DerridaRetaux.Analysis.LaplaceMildIdentity
import DerridaRetaux.Analysis.ShrinkingIntervalDerivative
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Abstract right-derivative closure for the Laplace transform of a mild
solution. -/
theorem hasDerivWithinAt_laplace_of_mildIdentity
    (u : ℝ → ℝ → ℝ) (p t transportDerivative : ℝ)
    (hmild : ∀ h : ℝ, 0 ≤ h →
      continuumLaplace (u (t + h)) p =
        shiftedHalfLineLaplace (u t) p h +
          ∫ s in t..t + h, (1 / 2 : ℝ) *
            shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
              (t + h - s))
    (htransport : HasDerivWithinAt (shiftedHalfLineLaplace (u t) p)
      transportDerivative (Ici 0) 0)
    (hG : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) *
        shiftedHalfLineLaplace (positiveSelfConvolution (u z.2)) p
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t))
    (hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable
      (fun s ↦ (1 / 2 : ℝ) *
        shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
          (t + h - s)) volume t (t + h)) :
    HasDerivWithinAt (fun h ↦ continuumLaplace (u (t + h)) p)
      (transportDerivative + (1 / 2 : ℝ) *
        continuumLaplace (positiveSelfConvolution (u t)) p)
      (Ici 0) 0 := by
  let G : ℝ → ℝ → ℝ := fun h s ↦ (1 / 2 : ℝ) *
    shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p (t + h - s)
  have hshrink := hasDerivWithinAt_shrinkingInterval G t hG hInt
  have hsum := htransport.add hshrink
  have hGzero : G 0 t = (1 / 2 : ℝ) *
      continuumLaplace (positiveSelfConvolution (u t)) p := by
    simp [G, shiftedHalfLineLaplace, continuumLaplace]
  rw [hGzero] at hsum
  apply hsum.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact hmild h hh
  · simp [G, shiftedHalfLineLaplace, continuumLaplace]

end

end DerridaRetaux
