import DerridaRetaux.Rigidity.ConstructedSolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The residual which vanishes for the physical-time Riccati solution. -/
def riccatiResidualNormalized (p : ℝ) (Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  (((t * p + 2) * Z t - t * p ^ 2) / t ^ 2)

theorem hasDerivAt_riccatiResidualNormalized
    (p : ℝ) (Z : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hZ : HasDerivAt Z
      ((2 / t) * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t) :
    HasDerivAt (riccatiResidualNormalized p Z)
      (((Z t + p) / 2) * riccatiResidualNormalized p Z t) t := by
  have hlinear : HasDerivAt (fun s : ℝ ↦ s * p + 2) p t := by
    convert (hasDerivAt_id t).mul_const p |>.add_const 2 using 1 <;> ring
  have hnum := (hlinear.mul hZ).sub ((hasDerivAt_id t).mul_const (p ^ 2))
  have hden : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;> simp [id_eq]
  have hquot := hnum.div hden (pow_ne_zero 2 ht.ne')
  convert hquot using 1
  · unfold riccatiResidualNormalized
    field_simp [ht.ne']
    ring

/-- The entrance asymptotic selects the rational solution of the singular
Riccati equation. -/
theorem riccati_eq_physicalTime_of_entrance
    (p : ℝ) (Z : ℝ → ℝ) (hp : 0 ≤ p)
    (hZ : ∀ t : ℝ, 0 < t → HasDerivAt Z
      ((2 / t) * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t)
    (hInt : ∀ t : ℝ, 0 < t → IntervalIntegrable Z volume 0 t)
    (hPhiZero : Tendsto (constructedPhi Z) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hResidualZero : Tendsto (riccatiResidualNormalized p Z)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ t : ℝ, 0 < t → Z t = t * p ^ 2 / (t * p + 2) := by
  let S := riccatiResidualNormalized p Z
  let E : ℝ → ℝ := fun t ↦ constructedPhi Z t * Real.exp (-p * t / 2)
  let F : ℝ → ℝ := fun t ↦ E t * S t
  have hZcont : ContinuousOn Z (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hZ t ht).continuousAt.continuousWithinAt
  have hSderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt S (((Z t + p) / 2) * S t) t := by
    intro t ht
    simpa only [S] using hasDerivAt_riccatiResidualNormalized p Z ht (hZ t ht)
  have hEderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt E (-((Z t + p) / 2) * E t) t := by
    intro t ht
    have hmeas : StronglyMeasurableAtFilter Z (𝓝 t) volume :=
      hZcont.stronglyMeasurableAtFilter isOpen_Ioi t ht
    have hPhi := hasDerivAt_constructedPhi Z t (hInt t ht) hmeas
      (hZ t ht).continuousAt
    have harg : HasDerivAt (fun s : ℝ ↦ -p * s / 2) (-p / 2) t := by
      convert ((hasDerivAt_const t (-p)).mul (hasDerivAt_id t) |>.div_const 2)
        using 1 <;> ring
    have hexp := (Real.hasDerivAt_exp (-p * t / 2)).comp t harg
    have hproduct := hPhi.mul hexp
    convert hproduct using 1 <;> simp only [E, Function.comp_apply] <;> ring
  have hFderiv : ∀ t : ℝ, 0 < t → HasDerivAt F 0 t := by
    intro t ht
    have hproduct := (hEderiv t ht).mul (hSderiv t ht)
    dsimp only [F]
    convert hproduct using 1 <;> ring
  have hFdiff : DifferentiableOn ℝ F (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hFderiv t ht).differentiableAt.differentiableWithinAt
  have hFderivZero : EqOn (deriv F) 0 (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hFderiv t ht).deriv
  have hExpZero : Tendsto (fun t : ℝ ↦ Real.exp (-p * t / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have harg : Tendsto (fun t : ℝ ↦ -p * t / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      convert (tendsto_const_nhds.mul hid).div_const (2 : ℝ) using 1 <;> ring
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp harg
  have hEZero : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [E, one_mul] using hPhiZero.mul hExpZero
  have hFZero : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hSZero : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [S] using hResidualZero
    change Tendsto (fun t : ℝ ↦ E t * S t) (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa only [mul_zero] using hEZero.mul hSZero
  intro t ht
  have hconst : ∀ s ∈ Ioi (0 : ℝ), F s = F t := by
    intro s hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected hFdiff hFderivZero hs ht
  have hevent : F =ᶠ[𝓝[>] (0 : ℝ)] fun _ ↦ F t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hconst s hs
  have hconstantZero : Tendsto (fun _ : ℝ ↦ F t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hFZero.congr' hevent
  have hFt : F t = 0 := by simpa using hconstantZero
  have hEt : 0 < E t := by
    dsimp only [E]
    exact mul_pos (constructedPhi_pos Z t) (Real.exp_pos _)
  have hSt : S t = 0 := by
    dsimp only [F] at hFt
    exact (mul_eq_zero.mp hFt).resolve_left hEt.ne'
  dsimp only [S, riccatiResidualNormalized] at hSt
  have hdenPos : 0 < t * p + 2 := by positivity
  field_simp [ht.ne'] at hSt
  exact (eq_div_iff hdenPos.ne').2 (by linarith)

end

end DerridaRetaux
