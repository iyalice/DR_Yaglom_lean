import DerridaRetaux.Basic.PMFBridge
import DerridaRetaux.Prelim.CubicMoment
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Cubic size-biased marginals

This file constructs the normalized law
`q♯(k) = h_m(k) q(k) / J` at every finite generation.  The construction is
total on `ℕ`: indices at which the cubic carrier vanishes receive mass zero.  In
particular, at binary arity both indices zero and one have zero size-biased mass.
-/

/-- The normalized cubic size bias of a critical tilted law with positive `J`. -/
def cubicSizeBiasedLaw
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) : ProbabilityMass where
  mass := fun k ↦
    cubicCarrier m k * normalizedTilt m p k / normalizedCubicMoment m p
  nonneg := fun k ↦ div_nonneg
    (mul_nonneg (cubicCarrier_nonneg m k hm)
      (normalizedTilt_nonneg m p (by omega) hcrit k)) hJ.le
  hasSum_one := by
    have hsum :=
      (normalizedCubicMoment_hasSum m p hm hcrit hthird).div_const
        (normalizedCubicMoment m p)
    simpa [hJ.ne'] using hsum

@[simp]
theorem cubicSizeBiasedLaw_apply
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    cubicSizeBiasedLaw m p hm hcrit hthird hJ k =
      cubicCarrier m k * normalizedTilt m p k / normalizedCubicMoment m p :=
  rfl

/-- The corresponding mathlib `PMF`, obtained through the lossless project bridge. -/
def cubicSizeBiasedPMF
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) : PMF ℕ :=
  (cubicSizeBiasedLaw m p hm hcrit hthird hJ).toPMF

@[simp]
theorem cubicSizeBiasedPMF_apply_toReal
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal =
      cubicCarrier m k * normalizedTilt m p k / normalizedCubicMoment m p := by
  exact ProbabilityMass.toPMF_apply_toReal
    (cubicSizeBiasedLaw m p hm hcrit hthird hJ) k

/-- The source marginal `q_n♯` for admissible profile data. -/
def spineMarginal (m : ℕ) (data : ProfileInitialData m) (n : ℕ) : ProbabilityMass :=
  cubicSizeBiasedLaw m (orbit m data.law n) data.arity
    (orbit_critical m data.law
      (le_trans (by norm_num) data.arity) data.critical n)
    (orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n)
    (normalizedCubicMoment_profile_orbit_pos m data n)

@[simp]
theorem spineMarginal_apply (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) :
    spineMarginal m data n k =
      cubicCarrier m k * normalizedTilt m (orbit m data.law n) k /
        normalizedCubicMoment m (orbit m data.law n) :=
  rfl

/-- Mathlib `PMF` form of the source marginal. -/
def spineMarginalPMF (m : ℕ) (data : ProfileInitialData m) (n : ℕ) : PMF ℕ :=
  (spineMarginal m data n).toPMF

@[simp]
theorem spineMarginalPMF_apply_toReal
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) :
    (spineMarginalPMF m data n k).toReal =
      cubicCarrier m k * normalizedTilt m (orbit m data.law n) k /
        normalizedCubicMoment m (orbit m data.law n) := by
  exact ProbabilityMass.toPMF_apply_toReal (spineMarginal m data n) k

/-- Every zero of the carrier is assigned zero size-biased mass. -/
theorem cubicSizeBiasedLaw_eq_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ)
    (hk : cubicCarrier m k = 0) :
    cubicSizeBiasedLaw m p hm hcrit hthird hJ k = 0 := by
  simp [hk]

/-- The zero row is absent for every arity. -/
@[simp]
theorem cubicSizeBiasedLaw_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) :
    cubicSizeBiasedLaw m p hm hcrit hthird hJ 0 = 0 := by
  apply cubicSizeBiasedLaw_eq_zero_of_carrier_eq_zero
  exact cubicCarrier_zero m

/-- At binary arity the additional zero-carrier row `k=1` is also absent. -/
@[simp]
theorem cubicSizeBiasedLaw_two_one
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hthird : TiltSummable 2 3 p)
    (hJ : 0 < normalizedCubicMoment 2 p) :
    cubicSizeBiasedLaw 2 p (by norm_num) hcrit hthird hJ 1 = 0 := by
  apply cubicSizeBiasedLaw_eq_zero_of_carrier_eq_zero
  exact cubicCarrier_two_one

/-- The orbit marginal is zero at every off-carrier index, without restricting
the definition to a subtype of the support. -/
theorem spineMarginal_eq_zero_of_carrier_eq_zero
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ)
    (hk : cubicCarrier m k = 0) :
    spineMarginal m data n k = 0 := by
  simp [spineMarginal_apply, hk]

@[simp]
theorem spineMarginal_zero (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    spineMarginal m data n 0 = 0 :=
  spineMarginal_eq_zero_of_carrier_eq_zero m data n 0 (cubicCarrier_zero m)

/-- Literal binary support boundary: the size-biased marginal is supported on
indices at least two. -/
theorem spineMarginal_two_eq_zero_of_lt_two
    (data : ProfileInitialData 2) (n k : ℕ) (hk : k < 2) :
    spineMarginal 2 data n k = 0 := by
  have hkCases : k = 0 ∨ k = 1 := by omega
  rcases hkCases with rfl | rfl
  · exact spineMarginal_zero 2 data n
  · exact spineMarginal_eq_zero_of_carrier_eq_zero
      2 data n 1 cubicCarrier_two_one

/-- On the positive carrier support, size-biased positivity is equivalent to
positivity of the underlying normalized tilted coefficient. -/
theorem cubicSizeBiasedLaw_pos_iff_of_carrier_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ)
    (hk : 0 < cubicCarrier m k) :
    0 < cubicSizeBiasedLaw m p hm hcrit hthird hJ k ↔
      0 < normalizedTilt m p k := by
  rw [cubicSizeBiasedLaw_apply]
  constructor
  · intro h
    have hnum : 0 < cubicCarrier m k * normalizedTilt m p k := by
      calc
        0 < (cubicCarrier m k * normalizedTilt m p k /
              normalizedCubicMoment m p) * normalizedCubicMoment m p :=
          mul_pos h hJ
        _ = cubicCarrier m k * normalizedTilt m p k := by
          exact div_mul_cancel₀ _ hJ.ne'
    by_contra hq
    have hqZero : normalizedTilt m p k = 0 :=
      le_antisymm (le_of_not_gt hq) (normalizedTilt_nonneg m p (by omega) hcrit k)
    rw [hqZero, mul_zero] at hnum
    exact (lt_irrefl 0) hnum
  · intro hq
    exact div_pos (mul_pos hk hq) hJ

end

end DerridaRetaux
