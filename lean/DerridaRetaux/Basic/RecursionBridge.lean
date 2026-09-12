import DerridaRetaux.Basic.Convolution
import DerridaRetaux.Model.Recursion

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace DerridaRetaux

/-!
# Agreement of the PMF and coefficient recursions

This file proves that the independent-sum construction in `Model.Recursion` has
the finite Cauchy coefficients developed in `Basic.Convolution`.  Consequently,
the PMF update `lawStep`, the bundled update `drStep`, and their orbit agree with
`drStepProb` and `coefficientOrbit`.
-/

noncomputable section

/-- The successor independent sum is the antidiagonal Cauchy sum pointwise. -/
theorem iidSum_succ_apply_antidiagonal (r : ℕ) (μ : PMF ℕ) (n : ℕ) :
    iidSum (r + 1) μ n =
      ∑ kl ∈ Finset.antidiagonal n, iidSum r μ kl.1 * μ kl.2 := by
  rw [iidSum_succ]
  change ((iidSum r μ).bind (fun x ↦ μ.bind (fun y ↦ PMF.pure (x + y)))) n = _
  rw [PMF.bind_apply]
  simp_rw [PMF.bind_apply, PMF.pure_apply, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  rw [tsum_eq_sum (s := Finset.antidiagonal n)]
  · apply Finset.sum_congr rfl
    intro kl hkl
    have hsum := Finset.mem_antidiagonal.mp hkl
    simp [hsum, mul_assoc]
  · intro kl hkl
    have hne : n ≠ kl.1 + kl.2 := by
      intro h
      exact hkl (Finset.mem_antidiagonal.mpr h.symm)
    simp [hne]

/-- The real coefficient of an `iidSum` is the corresponding convolution power. -/
theorem iidSum_apply_toReal (r : ℕ) (p : ProbabilityMass) (n : ℕ) :
    (iidSum r p.toPMF n).toReal = convPow r p n := by
  induction r generalizing n with
  | zero =>
      rw [iidSum_zero, convPow_zero]
      change (PMF.pure 0 n).toReal = diracSeq 0 n
      by_cases hn : n = 0 <;> simp [PMF.pure_apply, diracSeq, hn]
  | succ r ih =>
      rw [iidSum_succ_apply_antidiagonal, convPow_succ,
        conv_eq_sum_antidiagonal]
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro kl _
        rw [ENNReal.toReal_mul, ih, ProbabilityMass.toPMF_apply_toReal]
      · intro kl _
        exact ENNReal.mul_ne_top ((iidSum r p.toPMF).apply_ne_top kl.1)
          (p.toPMF.apply_ne_top kl.2)

/-- The `PMF` independent sum is the PMF view of the bundled convolution power. -/
theorem iidSum_eq_convPowProb_toPMF (r : ℕ) (p : ProbabilityMass) :
    iidSum r p.toPMF = (convPowProb r p).toPMF := by
  apply PMF.ext
  intro n
  apply (ENNReal.toReal_eq_toReal
    ((iidSum r p.toPMF).apply_ne_top n)
    ((convPowProb r p).toPMF.apply_ne_top n)).mp
  rw [iidSum_apply_toReal, ProbabilityMass.toPMF_apply_toReal,
    convPowProb_apply]

/-- Extracting real coefficients after `iidSum` gives the bundled convolution power. -/
theorem ofPMF_iidSum_eq_convPowProb (r : ℕ) (p : ProbabilityMass) :
    ProbabilityMass.ofPMF (iidSum r p.toPMF) = convPowProb r p := by
  apply ProbabilityMass.ext
  intro n
  rw [ProbabilityMass.ofPMF_apply, iidSum_apply_toReal, convPowProb_apply]

/-- The convolution representation for an arbitrary mathlib PMF. -/
theorem iidSum_apply_toReal_ofPMF (r : ℕ) (μ : PMF ℕ) (n : ℕ) :
    (iidSum r μ n).toReal = convPow r (ProbabilityMass.ofPMF μ) n := by
  simpa using iidSum_apply_toReal r (ProbabilityMass.ofPMF μ) n

/-- PMF equality form of the convolution representation for an arbitrary PMF. -/
theorem iidSum_eq_convPowProb_toPMF_ofPMF (r : ℕ) (μ : PMF ℕ) :
    iidSum r μ = (convPowProb r (ProbabilityMass.ofPMF μ)).toPMF := by
  simpa using iidSum_eq_convPowProb_toPMF r (ProbabilityMass.ofPMF μ)

/-- Real-bundle equality form of the convolution representation for an arbitrary PMF. -/
theorem ofPMF_iidSum_eq_convPowProb_ofPMF (r : ℕ) (μ : PMF ℕ) :
    ProbabilityMass.ofPMF (iidSum r μ) =
      convPowProb r (ProbabilityMass.ofPMF μ) := by
  simpa using ofPMF_iidSum_eq_convPowProb r (ProbabilityMass.ofPMF μ)

/-- Mapping natural predecessor merges precisely the atoms at zero and one. -/
theorem map_natPred_apply_zero (μ : PMF ℕ) :
    μ.map (fun total ↦ total - 1) 0 = μ 0 + μ 1 := by
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro a ha
    have ha0 : a ≠ 0 := by
      intro h
      apply ha
      simp [h]
    have ha1 : a ≠ 1 := by
      intro h
      apply ha
      simp [h]
    have hpred : 0 ≠ a - 1 := by omega
    simp [hpred]

/-- Away from zero, mapping natural predecessor simply shifts coefficients left. -/
theorem map_natPred_apply_succ (μ : PMF ℕ) (k : ℕ) :
    μ.map (fun total ↦ total - 1) (k + 1) = μ (k + 2) := by
  rw [PMF.map_apply, tsum_eq_single (k + 2)]
  · simp
  · intro a ha
    have hne : k + 1 ≠ a - 1 := by
      intro h
      apply ha
      omega
    simp [hne]

/-- The real coefficients of the PMF law step are exactly `drStepSeq`. -/
theorem lawStep_apply_toReal (m : ℕ) (p : ProbabilityMass) (k : ℕ) :
    (lawStep m p.toPMF k).toReal = drStepSeq m p k := by
  cases k with
  | zero =>
      rw [lawStep, map_natPred_apply_zero,
        ENNReal.toReal_add ((iidSum m p.toPMF).apply_ne_top 0)
          ((iidSum m p.toPMF).apply_ne_top 1),
        iidSum_apply_toReal, iidSum_apply_toReal]
      rfl
  | succ k =>
      rw [lawStep, map_natPred_apply_succ, iidSum_apply_toReal]
      rfl

/-- The PMF law step is the PMF view of the coefficient-level bundled step. -/
theorem lawStep_eq_drStepProb_toPMF (m : ℕ) (p : ProbabilityMass) :
    lawStep m p.toPMF = (drStepProb m p).toPMF := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal
    ((lawStep m p.toPMF).apply_ne_top k)
    ((drStepProb m p).toPMF.apply_ne_top k)).mp
  rw [lawStep_apply_toReal, ProbabilityMass.toPMF_apply_toReal,
    drStepProb_apply]

/-- The PMF-defined bundled step equals the direct coefficient construction. -/
theorem drStep_eq_drStepProb (m : ℕ) (p : ProbabilityMass) :
    drStep m p = drStepProb m p := by
  apply ProbabilityMass.ext
  intro k
  change (lawStep m p.toPMF k).toReal = drStepSeq m p k
  exact lawStep_apply_toReal m p k

/-- The law step representation for an arbitrary mathlib PMF. -/
theorem lawStep_eq_drStepProb_toPMF_ofPMF (m : ℕ) (μ : PMF ℕ) :
    lawStep m μ = (drStepProb m (ProbabilityMass.ofPMF μ)).toPMF := by
  simpa using lawStep_eq_drStepProb_toPMF m (ProbabilityMass.ofPMF μ)

/-- The recursively defined PMF-backed orbit equals the coefficient-level iterate. -/
theorem orbit_eq_coefficientOrbit (m : ℕ) (p : ProbabilityMass) (n : ℕ) :
    orbit m p n = coefficientOrbit m p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        orbit m p (n + 1) = drStep m (orbit m p n) := rfl
        _ = drStepProb m (orbit m p n) := drStep_eq_drStepProb m (orbit m p n)
        _ = drStepProb m (coefficientOrbit m p n) := congrArg (drStepProb m) ih
        _ = coefficientOrbit m p (n + 1) := (coefficientOrbit_succ m p n).symm

/-- Pointwise PMF form of `orbit_eq_coefficientOrbit`. -/
theorem orbit_toPMF_eq_coefficientOrbit_toPMF
    (m : ℕ) (p : ProbabilityMass) (n : ℕ) :
    (orbit m p n).toPMF = (coefficientOrbit m p n).toPMF := by
  rw [orbit_eq_coefficientOrbit]

end

end DerridaRetaux
