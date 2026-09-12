import DerridaRetaux.Analysis.ShiftedMomentBinomial
import DerridaRetaux.Analysis.ConvolutionContinuityOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- The closed triangular parameter domain of a forward Duhamel integral. -/
def closedDuhamelTriangle (t H : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ H ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}

/-- Continuity of a moving short moment throughout a compact forward
Duhamel triangle. -/
theorem continuousOn_shortMomentIntegral_triangle
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t H : ℝ) (hH : 0 ≤ H)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H)) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦
        ∫ y in (0 : ℝ)..(t + z.1 - z.2), y ^ r * v z.2 y)
      (closedDuhamelTriangle t H) := by
  let timeClamp : ℝ → ℝ := closedIntervalClamp t (t + H)
  let spaceClamp : ℝ → ℝ := closedIntervalClamp 0 H
  let V : ℝ → ℝ → ℝ := fun s x ↦ v (timeClamp s) (spaceClamp x)
  have htime : t ≤ t + H := by linarith
  have hmap : Continuous (fun p : ℝ × ℝ ↦
      (timeClamp p.1, spaceClamp p.2)) := by
    exact ((continuous_closedIntervalClamp t (t + H)).comp
      continuous_fst).prodMk
        ((continuous_closedIntervalClamp 0 H).comp continuous_snd)
  have hmaps : ∀ p : ℝ × ℝ,
      (timeClamp p.1, spaceClamp p.2) ∈
        Icc t (t + H) ×ˢ Icc (0 : ℝ) H := by
    intro p
    exact ⟨closedIntervalClamp_mem htime, closedIntervalClamp_mem hH⟩
  have hV : Continuous (Function.uncurry V) :=
    hv.comp_continuous hmap hmaps
  let f : (ℝ × ℝ) → ℝ → ℝ := fun z y ↦ y ^ r * V z.2 y
  have hf : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry_apply_pair]
    exact (continuous_snd.pow r).mul
      (hV.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have ha : Continuous (fun z : ℝ × ℝ ↦ t + z.1 - z.2) := by fun_prop
  have hJ : Continuous (fun z : ℝ × ℝ ↦
      ∫ y in (0 : ℝ)..(t + z.1 - z.2), y ^ r * V z.2 y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) hf ha
  apply hJ.continuousOn.congr
  intro z hz
  have hsbox : z.2 ∈ Icc t (t + H) :=
    ⟨hz.2.2.1, hz.2.2.2.trans (add_le_add_left hz.2.1 t)⟩
  have ha0 : 0 ≤ t + z.1 - z.2 := by linarith [hz.2.2.2]
  have haH : t + z.1 - z.2 ≤ H := by linarith [hz.2.1, hz.2.2.1]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le ha0] at hy
  have hybox : y ∈ Icc (0 : ℝ) H := ⟨hy.1, hy.2.trans haH⟩
  simp only [V, timeClamp, spaceClamp,
    closedIntervalClamp_eq_self hsbox,
    closedIntervalClamp_eq_self hybox]

/-- Moving tail moments are continuous throughout a compact forward
Duhamel triangle. -/
theorem continuousOn_halfLineTailMoment_triangle
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t H : ℝ) (hH : 0 ≤ H)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H))
    (hB : ContinuousOn (fun s : ℝ ↦ continuumMoment (v s) r)
      (Icc t (t + H))) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦ halfLineTailMoment (v z.2) r
        (t + z.1 - z.2)) (closedDuhamelTriangle t H) := by
  have hshort := continuousOn_shortMomentIntegral_triangle v r t H hH hv
  have hs : ContinuousOn (fun z : ℝ × ℝ ↦ continuumMoment (v z.2) r)
      (closedDuhamelTriangle t H) := by
    exact hB.comp continuous_snd.continuousOn fun z hz ↦
      ⟨hz.2.2.1, hz.2.2.2.trans (add_le_add_left hz.2.1 t)⟩
  simpa only [halfLineTailMoment] using hs.sub hshort

/-- Shifted moments are continuous throughout a compact forward Duhamel
triangle. -/
theorem continuousOn_shiftedHalfLineMoment_triangle
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t H : ℝ) (hH : 0 ≤ H)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H))
    (hB : ∀ k : ℕ, k ≤ r → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + H)))
    (hmom : ∀ s : ℝ, s ∈ Icc t (t + H) → ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0)) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment (v z.2) r
        (t + z.1 - z.2)) (closedDuhamelTriangle t H) := by
  let a : ℝ × ℝ → ℝ := fun z ↦ t + z.1 - z.2
  have ha : Continuous a := by fun_prop
  have htail : ∀ k ∈ Finset.range (r + 1), ContinuousOn
      (fun z : ℝ × ℝ ↦ halfLineTailMoment (v z.2) k (a z))
      (closedDuhamelTriangle t H) := by
    intro k hk
    exact continuousOn_halfLineTailMoment_triangle v k t H hH hv
      (hB k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hsum : ContinuousOn
      (fun z : ℝ × ℝ ↦ ∑ k ∈ Finset.range (r + 1),
        (r.choose k : ℝ) * (-a z) ^ (r - k) *
          halfLineTailMoment (v z.2) k (a z))
      (closedDuhamelTriangle t H) := by
    apply continuousOn_finset_sum
    intro k hk
    exact ((continuousOn_const.mul
      ((ha.neg.pow (r - k)).continuousOn)).mul (htail k hk))
  apply hsum.congr
  intro z hz
  have ha0 : 0 ≤ a z := by dsimp only [a]; linarith [hz.2.2.2]
  have hsbox : z.2 ∈ Icc t (t + H) :=
    ⟨hz.2.2.1, hz.2.2.2.trans (add_le_add_left hz.2.1 t)⟩
  simpa only [a] using
    (shiftedHalfLineMoment_eq_sum (v z.2) r ha0 (hmom z.2 hsbox))

end

end DerridaRetaux
