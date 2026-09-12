import DerridaRetaux.Analysis.HalfLineShiftLaplace
import DerridaRetaux.Analysis.ShiftedMomentTriangleContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Continuity of the moving short Laplace integral on a compact forward
Duhamel triangle. -/
theorem continuousOn_shortLaplaceIntegral_triangle
    (v : ℝ → ℝ → ℝ) (p t H : ℝ) (hH : 0 ≤ H)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H)) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦
        ∫ y in (0 : ℝ)..(t + z.1 - z.2),
          Real.exp (-(p * y)) * v z.2 y)
      (closedDuhamelTriangle t H) := by
  let timeClamp : ℝ → ℝ := closedIntervalClamp t (t + H)
  let spaceClamp : ℝ → ℝ := closedIntervalClamp 0 H
  let V : ℝ → ℝ → ℝ := fun s x ↦ v (timeClamp s) (spaceClamp x)
  have htime : t ≤ t + H := by linarith
  have hmap : Continuous (fun q : ℝ × ℝ ↦
      (timeClamp q.1, spaceClamp q.2)) := by
    exact ((continuous_closedIntervalClamp t (t + H)).comp
      continuous_fst).prodMk
        ((continuous_closedIntervalClamp 0 H).comp continuous_snd)
  have hmaps : ∀ q : ℝ × ℝ,
      (timeClamp q.1, spaceClamp q.2) ∈
        Icc t (t + H) ×ˢ Icc (0 : ℝ) H := by
    intro q
    exact ⟨closedIntervalClamp_mem htime, closedIntervalClamp_mem hH⟩
  have hV : Continuous (Function.uncurry V) :=
    hv.comp_continuous hmap hmaps
  let f : (ℝ × ℝ) → ℝ → ℝ := fun z y ↦
    Real.exp (-(p * y)) * V z.2 y
  have hf : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry_apply_pair]
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_snd).neg).mul
      (hV.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have ha : Continuous (fun z : ℝ × ℝ ↦ t + z.1 - z.2) := by
    fun_prop
  have hJ : Continuous (fun z : ℝ × ℝ ↦
      ∫ y in (0 : ℝ)..(t + z.1 - z.2),
        Real.exp (-(p * y)) * V z.2 y) :=
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

/-- Shifted half-line Laplace transforms are continuous throughout a compact
forward Duhamel triangle. -/
theorem continuousOn_shiftedHalfLineLaplace_triangle
    (v : ℝ → ℝ → ℝ) (p t H : ℝ) (hH : 0 ≤ H)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H))
    (hB : ContinuousOn (fun s : ℝ ↦ continuumLaplace (v s) p)
      (Icc t (t + H)))
    (hLap : ∀ s : ℝ, s ∈ Icc t (t + H) → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * v s x) (Ici 0)) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace (v z.2) p
        (t + z.1 - z.2)) (closedDuhamelTriangle t H) := by
  let a : ℝ × ℝ → ℝ := fun z ↦ t + z.1 - z.2
  have ha : Continuous a := by fun_prop
  have hshort := continuousOn_shortLaplaceIntegral_triangle v p t H hH hv
  have hfull : ContinuousOn
      (fun z : ℝ × ℝ ↦ continuumLaplace (v z.2) p)
      (closedDuhamelTriangle t H) := by
    exact hB.comp continuous_snd.continuousOn fun z hz ↦
      ⟨hz.2.2.1, hz.2.2.2.trans (add_le_add_left hz.2.1 t)⟩
  have hformula : ContinuousOn
      (fun z : ℝ × ℝ ↦ Real.exp (p * a z) *
        (continuumLaplace (v z.2) p -
          ∫ y in (0 : ℝ)..a z, Real.exp (-(p * y)) * v z.2 y))
      (closedDuhamelTriangle t H) := by
    exact ((Real.continuous_exp.comp
      (continuous_const.mul ha)).continuousOn).mul (hfull.sub hshort)
  apply hformula.congr
  intro z hz
  have ha0 : 0 ≤ a z := by dsimp only [a]; linarith [hz.2.2.2]
  have hsbox : z.2 ∈ Icc t (t + H) :=
    ⟨hz.2.2.1, hz.2.2.2.trans (add_le_add_left hz.2.1 t)⟩
  simpa only [a] using shiftedHalfLineLaplace_eq
    (v z.2) p ha0 (hLap z.2 hsbox)

end

end DerridaRetaux
