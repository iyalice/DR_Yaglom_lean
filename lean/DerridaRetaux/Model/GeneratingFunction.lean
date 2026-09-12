import DerridaRetaux.Basic.WeightedConvolution
import DerridaRetaux.Basic.RecursionBridge
import DerridaRetaux.Model.Tilted
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Summability-safe generating functions

Generating functions are defined through their coefficient series.  Every evaluation
theorem carries or derives summability at the evaluation point, so boundary values
such as `s = m` are never justified by an unproved analytic continuation.
-/

/-- Absolute summability of the generating series at `s`. -/
def GeneratingSummable (s : ℝ) (p : ProbabilityMass) : Prop :=
  Summable (powerScale s p)

/-- The generating function evaluated coefficientwise at `s`. -/
def generatingFunction (s : ℝ) (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, powerScale s p k

theorem generatingFunction_hasSum (s : ℝ) (p : ProbabilityMass)
    (h : GeneratingSummable s p) :
    HasSum (powerScale s p) (generatingFunction s p) :=
  h.hasSum

theorem generatingSummable_one (p : ProbabilityMass) : GeneratingSummable 1 p := by
  change Summable (fun k : ℕ ↦ (1 : ℝ) ^ k * p k)
  simpa using p.summable

@[simp]
theorem generatingFunction_one (p : ProbabilityMass) : generatingFunction 1 p = 1 := by
  simp [generatingFunction, powerScale]

theorem tiltSummable_zero_iff_generatingSummable (m : ℕ) (p : ProbabilityMass) :
    TiltSummable m 0 p ↔ GeneratingSummable (m : ℝ) p := by
  constructor
  · intro h
    change Summable (fun k : ℕ ↦ (k : ℝ) ^ 0 * (m : ℝ) ^ k * p k) at h
    change Summable (fun k : ℕ ↦ (m : ℝ) ^ k * p k)
    simpa only [pow_zero, one_mul] using h
  · intro h
    change Summable (fun k : ℕ ↦ (m : ℝ) ^ k * p k) at h
    change Summable (fun k : ℕ ↦ (k : ℝ) ^ 0 * (m : ℝ) ^ k * p k)
    simpa only [pow_zero, one_mul] using h

theorem tiltedPartition_eq_generatingFunction (m : ℕ) (p : ProbabilityMass) :
    tiltedPartition m p = generatingFunction (m : ℝ) p := by
  simp [tiltedPartition, tiltedMoment, generatingFunction, powerScale]

/-- Evaluation of the `m`-fold convolution is the `m`-th power of the evaluation. -/
theorem generatingFunction_convPow
    (r : ℕ) (s : ℝ) (p : ProbabilityMass) (h : GeneratingSummable s p) :
    ∑' k : ℕ, powerScale s (convPow r p) k = generatingFunction s p ^ r := by
  exact (powerScale_convPow_hasSum r s p (generatingFunction s p) h.hasSum).tsum_eq

/--
The exact cross-multiplied generating-function recursion from source equation
`eq:pgf`.  No division by `s` occurs, so the statement includes `s = 0`.
-/
theorem generatingFunction_drStep_cross
    (m : ℕ) (s : ℝ) (p : ProbabilityMass)
    (hp : GeneratingSummable s p)
    (hstep : GeneratingSummable s (drStepProb m p)) :
    s * generatingFunction s (drStepProb m p) =
      generatingFunction s p ^ m - p 0 ^ m + s * p 0 ^ m := by
  have hgHasSum :=
    powerScale_convPow_hasSum m s p (generatingFunction s p) hp.hasSum
  have hg : Summable (powerScale s (convPow m p)) := hgHasSum.summable
  have hgTail : Summable (fun n : ℕ ↦ powerScale s (convPow m p) (n + 1)) :=
    (summable_nat_add_iff 1).2 hg
  have hq : Summable (powerScale s (drStepProb m p)) := hstep
  have htail :
      s * ∑' n : ℕ, powerScale s (drStepProb m p) (n + 1) =
        ∑' n : ℕ, powerScale s (convPow m p) (n + 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [powerScale_apply, drStepProb_apply, drStepSeq_succ]
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
    ring
  change s * (∑' k : ℕ, powerScale s (drStepProb m p) k) = _
  rw [hq.tsum_eq_zero_add, mul_add, htail, ← hgHasSum.tsum_eq,
    hg.tsum_eq_zero_add, hgTail.tsum_eq_zero_add]
  simp only [powerScale_apply, drStepProb_apply, drStepSeq_zero, convPow_apply_zero,
    zero_pow, one_mul]
  ring

/-- The divided manuscript form of `eq:pgf`, valid away from `s = 0`. -/
theorem generatingFunction_drStep
    (m : ℕ) (s : ℝ) (p : ProbabilityMass)
    (hp : GeneratingSummable s p)
    (hstep : GeneratingSummable s (drStepProb m p))
    (hs : s ≠ 0) :
    generatingFunction s (drStepProb m p) =
      (generatingFunction s p ^ m - p 0 ^ m) / s + p 0 ^ m := by
  rw [← sub_eq_iff_eq_add]
  apply (eq_div_iff hs).2
  calc
    (generatingFunction s (drStepProb m p) - p 0 ^ m) * s =
        s * generatingFunction s (drStepProb m p) - s * p 0 ^ m := by ring
    _ = generatingFunction s p ^ m - p 0 ^ m := by
      rw [generatingFunction_drStep_cross m s p hp hstep]
      ring

/-- `eq:pgf` for the paper-facing independent-copy law step, without division. -/
theorem generatingFunction_paperStep_cross
    (m : ℕ) (s : ℝ) (p : ProbabilityMass)
    (hp : GeneratingSummable s p)
    (hstep : GeneratingSummable s (drStep m p)) :
    s * generatingFunction s (drStep m p) =
      generatingFunction s p ^ m - p 0 ^ m + s * p 0 ^ m := by
  rw [drStep_eq_drStepProb] at hstep ⊢
  exact generatingFunction_drStep_cross m s p hp hstep

/-- The divided paper-facing form of `eq:pgf`, valid for `s ≠ 0`. -/
theorem generatingFunction_paperStep
    (m : ℕ) (s : ℝ) (p : ProbabilityMass)
    (hp : GeneratingSummable s p)
    (hstep : GeneratingSummable s (drStep m p))
    (hs : s ≠ 0) :
    generatingFunction s (drStep m p) =
      (generatingFunction s p ^ m - p 0 ^ m) / s + p 0 ^ m := by
  rw [drStep_eq_drStepProb] at hstep ⊢
  exact generatingFunction_drStep m s p hp hstep hs

/-- Cross-multiplied `eq:pgf` between two successive generations. -/
theorem generatingFunction_orbit_succ_cross
    (m n : ℕ) (s : ℝ) (p₀ : ProbabilityMass)
    (hn : GeneratingSummable s (orbit m p₀ n))
    (hsucc : GeneratingSummable s (orbit m p₀ (n + 1))) :
    s * generatingFunction s (orbit m p₀ (n + 1)) =
      generatingFunction s (orbit m p₀ n) ^ m - orbit m p₀ n 0 ^ m +
        s * orbit m p₀ n 0 ^ m := by
  rw [orbit_succ] at hsucc ⊢
  exact generatingFunction_paperStep_cross m s (orbit m p₀ n) hn hsucc

end

end DerridaRetaux
