import DerridaRetaux.Analysis.MomentConvergenceFromLocal
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Continuous projection of the line onto the compact interval `[0,R]`. -/
def nonnegativeIntervalClamp (R x : ℝ) : ℝ := max 0 (min R x)

theorem continuous_nonnegativeIntervalClamp (R : ℝ) :
    Continuous (nonnegativeIntervalClamp R) := by
  exact continuous_const.max (continuous_const.min continuous_id)

theorem nonnegativeIntervalClamp_mem {R x : ℝ} (hR : 0 ≤ R) :
    nonnegativeIntervalClamp R x ∈ Icc (0 : ℝ) R := by
  constructor
  · exact le_max_left _ _
  · exact max_le hR (min_le_left _ _)

@[simp] theorem nonnegativeIntervalClamp_eq_self {R x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) R) :
    nonnegativeIntervalClamp R x = x := by
  simp [nonnegativeIntervalClamp, hx.1, hx.2]

/-- On a compact time interval, joint continuity of a half-line density
implies continuity of every compactly truncated polynomial moment. -/
theorem continuousOn_compactMomentIntegral
    (u : ℝ → ℝ → ℝ) (r : ℕ) (eta T R : ℝ) (hR : 0 ≤ R)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R)) :
    ContinuousOn
      (fun t : ℝ ↦ ∫ x in Icc (0 : ℝ) R, x ^ r * u t x)
      (Icc eta T) := by
  let clamp : ℝ → ℝ := nonnegativeIntervalClamp R
  have hclamp : Continuous clamp := continuous_nonnegativeIntervalClamp R
  let f : ↥(Icc eta T) → ℝ → ℝ :=
    fun t x ↦ clamp x ^ r * u t (clamp x)
  have hmap : Continuous (fun p : ↥(Icc eta T) × ℝ ↦
      (((p.1 : ↥(Icc eta T)) : ℝ), clamp p.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk (hclamp.comp continuous_snd)
  have hmaps : ∀ p : ↥(Icc eta T) × ℝ,
      (((p.1 : ↥(Icc eta T)) : ℝ), clamp p.2) ∈
        Icc eta T ×ˢ Icc (0 : ℝ) R := by
    intro p
    exact ⟨p.1.property, nonnegativeIntervalClamp_mem hR⟩
  have hu' : Continuous
      (fun p : ↥(Icc eta T) × ℝ ↦ u p.1 (clamp p.2)) := by
    exact hu.comp_continuous hmap hmaps
  have hpow : Continuous
      (fun p : ↥(Icc eta T) × ℝ ↦ clamp p.2 ^ r) := by
    exact (hclamp.comp continuous_snd).pow r
  have hf : Continuous (Function.uncurry f) := by
    exact hpow.mul hu'
  have hint := continuous_parametric_integral_of_continuous (μ := volume) hf (s := Icc (0 : ℝ) R) isCompact_Icc
  rw [continuousOn_iff_continuous_restrict]
  apply hint.congr
  intro t
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp only [f, clamp, Function.uncurry_apply_pair]
  rw [nonnegativeIntervalClamp_eq_self hx]

end

end DerridaRetaux
