import DerridaRetaux.Basic.ProbabilityMass
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option autoImplicit false

open ENNReal

namespace DerridaRetaux

/-!
# Bridge to mathlib probability mass functions

The paper-facing foundation keeps real coefficients and explicit real summability.
This file gives a lossless bridge to mathlib's `PMF ℕ` for law-level constructions;
it does not replace `ProbabilityMass` in any source-facing statement.
-/

/-- Regard a real `ProbabilityMass` as a mathlib `PMF`. -/
noncomputable def ProbabilityMass.toPMF (p : ProbabilityMass) : PMF ℕ :=
  ⟨fun k ↦ ENNReal.ofReal (p k), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg p.nonneg p.summable]
    simp [p.tsum_eq_one])⟩

@[simp] theorem ProbabilityMass.toPMF_apply_toReal (p : ProbabilityMass) (k : ℕ) :
    (p.toPMF k).toReal = p k := by
  change (ENNReal.ofReal (p k)).toReal = p k
  exact ENNReal.toReal_ofReal (p.nonneg k)

@[simp] theorem ProbabilityMass.toPMF_apply_ofReal (p : ProbabilityMass) (k : ℕ) :
    p.toPMF k = ENNReal.ofReal (p k) := by
  rfl

/-- Extract the real coefficients of a mathlib `PMF`. -/
noncomputable def ProbabilityMass.ofPMF (p : PMF ℕ) : ProbabilityMass where
  mass := fun k ↦ (p k).toReal
  nonneg := fun k ↦ ENNReal.toReal_nonneg
  hasSum_one := by
    have hsum : ∑' k : ℕ, (p k).toReal = 1 := by
      rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top)]
      simp
    have h := ENNReal.hasSum_toReal p.tsum_coe_ne_top
    rwa [hsum] at h

@[simp] theorem ProbabilityMass.ofPMF_apply (p : PMF ℕ) (k : ℕ) :
    ProbabilityMass.ofPMF p k = (p k).toReal :=
  rfl

/-- The real-to-PMF-to-real round trip is definitionally faithful pointwise. -/
@[simp] theorem ProbabilityMass.ofPMF_toPMF (p : ProbabilityMass) :
    ProbabilityMass.ofPMF p.toPMF = p := by
  apply ProbabilityMass.ext
  intro k
  exact p.toPMF_apply_toReal k

/-- The PMF-to-real-to-PMF round trip loses no probability mass. -/
@[simp] theorem ProbabilityMass.toPMF_ofPMF (p : PMF ℕ) :
    (ProbabilityMass.ofPMF p).toPMF = p := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal
    (((ProbabilityMass.ofPMF p).toPMF).apply_ne_top k)
    (p.apply_ne_top k)).mp
  simp

end DerridaRetaux
