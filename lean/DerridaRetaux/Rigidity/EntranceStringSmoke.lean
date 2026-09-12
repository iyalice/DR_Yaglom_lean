import DerridaRetaux.Rigidity.EntranceStringBase
import Mathlib.Tactic

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-!
# Nonvacuity check for the Volterra interface

The finite atomic string below is not the manuscript's model string and does not have
infinite mass at its right endpoint.  Its sole purpose is to show constructively that
the approved entrance-normalized Volterra predicate supports a nonzero measure, a
nonconstant solution, and a nonzero integral term.
-/

/-- A nonzero finite atomic string used only for the Volterra nonvacuity check. -/
def volterraSmokeString : EntranceString where
  mass := Measure.dirac (-1 : ℝ)
  endpoint := 0

/-- A nonconstant normalized solution for `volterraSmokeString` at `lambda = -1`. -/
def volterraSmokeSolution (x : ℝ) : ℝ :=
  1 + max (x + 1) 0

theorem continuous_volterraSmokeSolution : Continuous volterraSmokeSolution := by
  unfold volterraSmokeSolution
  fun_prop

theorem tendsto_volterraSmokeSolution_atBot :
    Tendsto volterraSmokeSolution atBot (𝓝 1) := by
  have h : volterraSmokeSolution =ᶠ[atBot] fun _ : ℝ ↦ 1 := by
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    simp [volterraSmokeSolution, max_eq_right (by linarith : x + 1 ≤ 0)]
  exact tendsto_const_nhds.congr' h.symm

theorem volterraSmokeString_isEntranceType : IsEntranceType volterraSmokeString := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Measure.dirac_ne_zero
  · intro b hb
    change Measure.dirac (-1 : ℝ) (Iic b) < ⊤
    rw [Measure.dirac_apply]
    by_cases h : (-1 : ℝ) ∈ Iic b <;> simp [h]
  · change Measure.dirac (-1 : ℝ) (Ioi 0) = 0
    rw [Measure.dirac_apply]
    simp
  · refine ⟨-(1 : ℝ) / 2, ?_, ?_, integrable_dirac.integrableOn⟩
    · change -(1 : ℝ) / 2 < 0
      norm_num
    change 0 < Measure.dirac (-1 : ℝ) (Iic (-(1 : ℝ) / 2))
    rw [Measure.dirac_apply_of_mem (by norm_num : (-1 : ℝ) ∈ Iic (-(1 : ℝ) / 2))]
    norm_num

theorem volterraSmokeString_hasSecondEntranceMoment :
    HasSecondEntranceMoment volterraSmokeString := by
  intro b hb
  exact integrable_dirac.integrableOn

theorem volterraSmokeSolution_satisfies :
    IsEntranceNormalizedVolterraSolution
      volterraSmokeString (-1) volterraSmokeSolution := by
  refine
    ⟨continuous_volterraSmokeSolution.continuousOn,
      tendsto_volterraSmokeSolution_atBot, ?_⟩
  intro xi hxi
  refine ⟨integrable_dirac.integrableOn, ?_⟩
  change volterraSmokeSolution xi =
    1 - (-1 : ℝ) *
      ∫ v in Iic xi, (xi - v) * volterraSmokeSolution v ∂Measure.dirac (-1)
  rw [setIntegral_dirac]
  by_cases h : (-1 : ℝ) ≤ xi
  · simp [Set.mem_Iic, h, volterraSmokeSolution,
      max_eq_left (by linarith : 0 ≤ xi + 1)]
    ring
  · have hlt : xi < -1 := lt_of_not_ge h
    simp [Set.mem_Iic, h, volterraSmokeSolution,
      max_eq_right (by linarith : xi + 1 ≤ 0)]

theorem volterraSmokeSolution_nonconstant :
    volterraSmokeSolution (-2) ≠ volterraSmokeSolution (-(1 : ℝ) / 2) := by
  norm_num [volterraSmokeSolution]

theorem volterraSmokeIntegral_nonzero :
    (∫ v in Iic (-(1 : ℝ) / 2),
      (-(1 : ℝ) / 2 - v) * volterraSmokeSolution v ∂volterraSmokeString.mass) = 1 / 2 := by
  change (∫ v in Iic (-(1 : ℝ) / 2),
    (-(1 : ℝ) / 2 - v) * volterraSmokeSolution v ∂Measure.dirac (-1)) = 1 / 2
  rw [setIntegral_dirac]
  norm_num [volterraSmokeSolution]

end

end DerridaRetaux
