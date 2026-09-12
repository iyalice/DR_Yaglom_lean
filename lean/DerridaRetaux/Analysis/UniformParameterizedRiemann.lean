import DerridaRetaux.Analysis.TimeRiemannLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators Interval

namespace DerridaRetaux

noncomputable section

/-- Left Riemann sums on the unit interval converge uniformly over an
arbitrary compact metric parameter set. -/
theorem latticeLeftRiemannSum_unit_uniform_on_compact_parameter
    {P : Type*} [PseudoMetricSpace P]
    (K : Set P) (hK : IsCompact K) (G : P × ℝ → ℝ)
    (hG : ContinuousOn G (K ×ˢ Icc (0 : ℝ) 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      ∀ p ∈ K,
        |latticeLeftRiemannSum (fun z ↦ G (p, z)) 1 mesh -
          ∫ z in (0 : ℝ)..1, G (p, z)| < ε := by
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := half_pos hε
  have hGuniform : UniformContinuousOn G
      (K ×ˢ Icc (0 : ℝ) 1) :=
    (hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hG
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hGuniform η hη
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt δ⁻¹
  refine ⟨max M₀ 1, ?_⟩
  intro mesh hmesh p hp
  have hM₀mesh : M₀ ≤ mesh := (le_max_left M₀ 1).trans hmesh
  have hmeshPos : 0 < mesh := (le_max_right M₀ 1).trans hmesh
  have hmeshReal : (0 : ℝ) < (mesh : ℝ) := by exact_mod_cast hmeshPos
  have hmeshNe : (mesh : ℝ) ≠ 0 := hmeshReal.ne'
  have hinvlt : (mesh : ℝ)⁻¹ < δ := by
    apply (inv_lt_comm₀ hmeshReal hδ).2
    exact hM₀.trans_le (by exact_mod_cast hM₀mesh)
  let a : ℕ → ℝ := fun j ↦ (j : ℝ) / (mesh : ℝ)
  have ha_mono : ∀ j : ℕ, a j ≤ a (j + 1) := by
    intro j
    dsimp only [a]
    apply div_le_div_of_nonneg_right _ hmeshReal.le
    exact_mod_cast Nat.le_succ j
  have ha_unit : ∀ {j : ℕ}, j ≤ mesh → a j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    constructor
    · exact div_nonneg (Nat.cast_nonneg j) hmeshReal.le
    · rw [div_le_one hmeshReal]
      exact_mod_cast hj
  have hslice : ContinuousOn (fun z : ℝ ↦ G (p, z))
      (Icc (0 : ℝ) 1) := by
    apply hG.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z hz
    exact ⟨hp, hz⟩
  have hpartition :
      ∑ j ∈ Finset.range mesh,
          ∫ z in a j..a (j + 1), G (p, z) =
        ∫ z in (0 : ℝ)..1, G (p, z) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun z : ℝ ↦ G (p, z)) (a := a) (n := mesh) (μ := volume)
      (fun j hj ↦
        (hslice.mono fun z hz ↦
          ⟨(ha_unit (Nat.le_of_lt hj)).1.trans hz.1,
            hz.2.trans (ha_unit (Nat.succ_le_iff.mpr hj)).2⟩).intervalIntegrable_of_Icc
          (ha_mono j))
    simpa only [a, Nat.cast_zero, zero_div, Nat.cast_add,
      Nat.cast_one, add_div, div_self hmeshNe] using hsum
  have hcell : ∀ j < mesh,
      |(mesh : ℝ)⁻¹ * G (p, a j) -
        ∫ z in a j..a (j + 1), G (p, z)| ≤
        η * (mesh : ℝ)⁻¹ := by
    intro j hj
    have hstep : a (j + 1) - a j = (mesh : ℝ)⁻¹ := by
      dsimp only [a]
      push_cast
      field_simp only [hmeshNe]
      ring
    have hconst : (mesh : ℝ)⁻¹ * G (p, a j) =
        ∫ _z in a j..a (j + 1), G (p, a j) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, hstep]
    have hconstInt : IntervalIntegrable (fun _z : ℝ ↦ G (p, a j))
        volume (a j) (a (j + 1)) := continuous_const.intervalIntegrable _ _
    have hcellSubset : Icc (a j) (a (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
      intro z hz
      exact ⟨(ha_unit (Nat.le_of_lt hj)).1.trans hz.1,
        hz.2.trans (ha_unit (Nat.succ_le_iff.mpr hj)).2⟩
    have hsliceInt : IntervalIntegrable (fun z : ℝ ↦ G (p, z))
        volume (a j) (a (j + 1)) :=
      (hslice.mono hcellSubset).intervalIntegrable_of_Icc (ha_mono j)
    rw [hconst, ← intervalIntegral.integral_sub hconstInt hsliceInt]
    calc
      |∫ z in a j..a (j + 1), G (p, a j) - G (p, z)| =
          ‖∫ z in a j..a (j + 1), G (p, a j) - G (p, z)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ η * |a (j + 1) - a j| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro z hz
        rw [uIoc_of_le (ha_mono j)] at hz
        have hzUnit : z ∈ Icc (0 : ℝ) 1 :=
          hcellSubset ⟨hz.1.le, hz.2⟩
        have hd : dist (p, a j) (p, z) < δ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
            Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
          calc
            z - a j ≤ a (j + 1) - a j := sub_le_sub_right hz.2 _
            _ = (mesh : ℝ)⁻¹ := hstep
            _ < δ := hinvlt
        have hpj : (p, a j) ∈ K ×ˢ Icc (0 : ℝ) 1 :=
          ⟨hp, ha_unit (Nat.le_of_lt hj)⟩
        have hpz : (p, z) ∈ K ×ˢ Icc (0 : ℝ) 1 := ⟨hp, hzUnit⟩
        simpa only [Real.norm_eq_abs, Real.dist_eq] using
          (le_of_lt (hmod (p, a j) hpj (p, z) hpz hd))
      _ = η * (mesh : ℝ)⁻¹ := by
        congr 1
        rw [hstep, abs_of_pos (inv_pos.mpr hmeshReal)]
  rw [latticeLeftRiemannSum, one_mul, ← hpartition,
    ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range mesh,
        ((mesh : ℝ)⁻¹ * G (p, (j : ℝ) / (mesh : ℝ)) -
          ∫ z in a j..a (j + 1), G (p, z))| ≤
        ∑ j ∈ Finset.range mesh,
          |(mesh : ℝ)⁻¹ * G (p, (j : ℝ) / (mesh : ℝ)) -
            ∫ z in a j..a (j + 1), G (p, z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range mesh, η * (mesh : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [a] using hcell j (Finset.mem_range.mp hj)
    _ = η := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp only [hmeshNe]
      ring
    _ < ε := half_lt_self hε

end

end DerridaRetaux
