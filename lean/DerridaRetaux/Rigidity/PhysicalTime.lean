import DerridaRetaux.Rigidity.StringCoordinates
import DerridaRetaux.Rigidity.ModelString
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Recovering the physical time coordinate

This file isolates the elementary ODE step on source lines 1012--1019.  Once
string identification supplies `Y = ξ² / d`, the already proved coordinate
identity `ξ' = Y` becomes `ξ' = ξ² / d`.  The entrance limit at time zero
removes the integration constant; no rigidity or inverse-spectral conclusion
is hidden in the statements below.
-/

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The Riccati coordinate with entrance limit `-∞` is exactly `-d/t`.

This is the integration-constant argument in source lines 1015--1018. -/
theorem physicalTimeCoordinate_eq_neg_div
    (d : ℝ) (xi : ℝ → ℝ)
    (hd : 0 < d)
    (hxiNeg : ∀ t : ℝ, 0 < t → xi t < 0)
    (hxiDeriv : ∀ t : ℝ, 0 < t →
      HasDerivAt xi (xi t ^ 2 / d) t)
    (hxiZero : Tendsto xi (𝓝[>] (0 : ℝ)) atBot) :
    ∀ t : ℝ, 0 < t → xi t = -d / t := by
  let firstIntegral : ℝ → ℝ := fun s ↦ d / xi s + s
  have hfirstDeriv : ∀ s : ℝ, 0 < s →
      HasDerivAt firstIntegral 0 s := by
    intro s hs
    have hxiNe : xi s ≠ 0 := (hxiNeg s hs).ne
    have hquot := (hasDerivAt_const s d).div (hxiDeriv s hs) hxiNe
    have hadd := hquot.add (hasDerivAt_id s)
    convert hadd using 1
    all_goals field_simp [hd.ne', hxiNe]
  have hfirstDiff : DifferentiableOn ℝ firstIntegral (Ioi (0 : ℝ)) := by
    intro s hs
    exact (hfirstDeriv s hs).differentiableAt.differentiableWithinAt
  have hfirstDerivZero : EqOn (deriv firstIntegral) 0 (Ioi (0 : ℝ)) := by
    intro s hs
    exact (hfirstDeriv s hs).deriv
  have hfirstZero : Tendsto firstIntegral (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hinv : Tendsto (fun s : ℝ ↦ (xi s)⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_inv_atBot_zero.comp hxiZero
    have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hmul : Tendsto (fun s : ℝ ↦ d * (xi s)⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 (d * 0)) :=
      tendsto_const_nhds.mul hinv
    have hsum : Tendsto (fun s : ℝ ↦ d * (xi s)⁻¹ + s)
        (𝓝[>] (0 : ℝ)) (𝓝 (d * 0 + 0)) :=
      hmul.add hid
    simpa [firstIntegral, div_eq_mul_inv] using hsum
  intro t ht
  have hconst : ∀ s ∈ Ioi (0 : ℝ), firstIntegral s = firstIntegral t := by
    intro s hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected
      hfirstDiff hfirstDerivZero hs ht
  have hevent : firstIntegral =ᶠ[𝓝[>] (0 : ℝ)] fun _ ↦ firstIntegral t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hconst s hs
  have hconstZero : Tendsto (fun _ : ℝ ↦ firstIntegral t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hfirstZero.congr' hevent
  have hvalue : firstIntegral t = 0 := by
    simpa using hconstZero
  dsimp [firstIntegral] at hvalue
  have hxiNe : xi t ≠ 0 := (hxiNeg t ht).ne
  field_simp [hxiNe, ht.ne'] at hvalue ⊢
  nlinarith

/-- Once density comparison gives `Y = ξ²/d`, the physical scale is `d/t²`. -/
theorem physicalTimeScale_eq
    (d : ℝ) (xi Y : ℝ → ℝ)
    (hd : 0 < d)
    (hxi : ∀ t : ℝ, 0 < t → xi t = -d / t)
    (hYxi : ∀ t : ℝ, 0 < t → Y t = xi t ^ 2 / d) :
    ∀ t : ℝ, 0 < t → Y t = d / t ^ 2 := by
  intro t ht
  rw [hYxi t ht, hxi t ht]
  field_simp [hd.ne', ht.ne']
  ring

/-- The identity `Y' = -A₀Y` then fixes the zeroth moment as `2/t`. -/
theorem physicalTimeZerothMoment_eq
    (d : ℝ) (Y A0 : ℝ → ℝ)
    (hd : 0 < d)
    (hY : ∀ t : ℝ, 0 < t → Y t = d / t ^ 2)
    (hYDeriv : ∀ t : ℝ, 0 < t →
      HasDerivAt Y (-A0 t * Y t) t) :
    ∀ t : ℝ, 0 < t → A0 t = 2 / t := by
  intro t ht
  have hpow : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1
    all_goals simp [id_eq]
  have hquot := (hasDerivAt_const t d).div hpow
    (pow_ne_zero 2 ht.ne')
  have hexplicit : HasDerivAt (fun s : ℝ ↦ d / s ^ 2)
      (-2 * d / t ^ 3) t := by
    convert hquot using 1
    field_simp [ht.ne']
    ring
  have hevent : (fun s : ℝ ↦ d / s ^ 2) =ᶠ[𝓝 t] Y := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hY s hs).symm
  have hYExplicit : HasDerivAt Y (-2 * d / t ^ 3) t :=
    hexplicit.congr_of_eventuallyEq hevent.symm
  have hderivEq := (hYDeriv t ht).unique hYExplicit
  rw [hY t ht] at hderivEq
  have hscaled := congrArg (fun z : ℝ ↦ z * (-t ^ 2 / d)) hderivEq
  field_simp [hd.ne', ht.ne'] at hscaled ⊢
  have hfactorNe : t ^ 2 * d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ht.ne') hd.ne'
  apply mul_left_cancel₀ hfactorNe
  calc
    (t ^ 2 * d) * (A0 t * t) = A0 t * t ^ 3 * d := by ring
    _ = A0 t * (t ^ 3 * d) := by ring
    _ = 2 * d * t ^ 2 := hscaled
    _ = t ^ 2 * d * 2 := by ring

/-- The explicit physical-time expression occurring in source line 1022. -/
def physicalTimePhi (p t : ℝ) : ℝ :=
  (1 + p * t / 2) * Real.exp (-p * t / 2)

/-- Equality with the model endpoint derivative recovers the source formula
for `Phi`, once the physical coordinate has been fixed. -/
theorem physicalTimePhi_eq_of_modelDerivative
    (d p t Phi : ℝ)
    (hd : 0 < d)
    (hf : modelStringEndpointSolutionDeriv d p (-d / t) = -Phi) :
    Phi = physicalTimePhi p t := by
  have harg : d * p / (2 * (-d / t)) = -p * t / 2 := by
    field_simp [hd.ne']
    ring
  rw [modelStringEndpointSolutionDeriv, harg] at hf
  dsimp [physicalTimePhi]
  linarith

/-- Direct derivative of the recovered `Phi` formula. -/
theorem hasDerivAt_physicalTimePhi (p t : ℝ) :
    HasDerivAt (physicalTimePhi p)
      (-(t * p ^ 2 / 4) * Real.exp (-p * t / 2)) t := by
  have hlinear : HasDerivAt (fun s : ℝ ↦ 1 + p * s / 2) (p / 2) t := by
    convert (hasDerivAt_const t 1).add
      ((hasDerivAt_const t p).mul (hasDerivAt_id t) |>.div_const 2) using 1
    all_goals ring
  have hexponent : HasDerivAt (fun s : ℝ ↦ -p * s / 2) (-p / 2) t := by
    convert ((hasDerivAt_const t (-p)).mul (hasDerivAt_id t) |>.div_const 2)
      using 1
    all_goals ring
  have hexp := (Real.hasDerivAt_exp (-p * t / 2)).comp t hexponent
  have hprod := hlinear.mul hexp
  convert hprod using 1
  simp only [Function.comp_apply]
  ring

/-- The logarithmic derivative relation for `Phi` recovers
`Z(t,p)=t p²/(tp+2)`. -/
theorem physicalTimeLaplaceGap_eq
    (p : ℝ) (Phi Z : ℝ → ℝ)
    (hp : 0 ≤ p)
    (hPhi : ∀ t : ℝ, 0 < t → Phi t = physicalTimePhi p t)
    (hPhiDeriv : ∀ t : ℝ, 0 < t →
      HasDerivAt Phi (-(1 / 2 : ℝ) * Z t * Phi t) t) :
    ∀ t : ℝ, 0 < t → Z t = t * p ^ 2 / (t * p + 2) := by
  intro t ht
  have hevent : physicalTimePhi p =ᶠ[𝓝 t] Phi := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hPhi s hs).symm
  have hPhiExplicit : HasDerivAt Phi
      (-(t * p ^ 2 / 4) * Real.exp (-p * t / 2)) t :=
    (hasDerivAt_physicalTimePhi p t).congr_of_eventuallyEq hevent.symm
  have hderivEq := (hPhiDeriv t ht).unique hPhiExplicit
  rw [hPhi t ht, physicalTimePhi] at hderivEq
  have hexpNe : Real.exp (-p * t / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hcancel :
      (-(1 / 2 : ℝ) * Z t * (1 + p * t / 2)) =
        -(t * p ^ 2 / 4) := by
    apply mul_right_cancel₀ hexpNe
    calc
      (-(1 / 2 : ℝ) * Z t * (1 + p * t / 2)) *
          Real.exp (-p * t / 2) =
        -(1 / 2 : ℝ) * Z t *
          ((1 + p * t / 2) * Real.exp (-p * t / 2)) := by ring
      _ = -(t * p ^ 2 / 4) * Real.exp (-p * t / 2) := hderivEq
  have hdenPos : 0 < t * p + 2 := by positivity
  field_simp [hdenPos.ne'] at hcancel ⊢
  ring_nf at hcancel ⊢
  linarith

/-- Substituting `A₀=2/t` and the recovered gap gives the rational Laplace
transform in the first half of `eq:rigidprofile`. -/
theorem physicalTimeLaplaceTransform_eq
    (t p A0 Z U : ℝ)
    (ht : 0 < t) (hp : 0 ≤ p)
    (hA0 : A0 = 2 / t)
    (hZ : Z = t * p ^ 2 / (t * p + 2))
    (hU : U = A0 - p + Z) :
    U = 4 / (t * (t * p + 2)) := by
  have hdenPos : 0 < t * p + 2 := by positivity
  rw [hU, hA0, hZ]
  field_simp [ht.ne', hdenPos.ne']
  ring

end

end DerridaRetaux
