import DerridaRetaux.Analysis.ProfileConsequences
import DerridaRetaux.Analysis.TemporalSmoothing
import DerridaRetaux.Analysis.TruncatedSmoothingBounds
import Mathlib.Tactic

/-!
# Vanishing of the higher-order density source

The source orders `r ≥ 3` are packaged in `densityE`.  On a positive time
annulus their Duhamel contribution is one order smaller than the quadratic
term after multiplication by the profile scale squared.  This file first
proves the exact finite bound and then a moving-index limit usable in U45.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- A finite higher-order Duhamel segment is bounded by its length times the
order-four source bound at its left endpoint. -/
theorem densityHigherSegment_supLE_of_order_four
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (CE : ℝ) (hCE : 0 ≤ CE)
    (hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4))
    {a n : ℕ} (_han : a ≤ n) :
    SupLE (densityHigherSegment m p₀ a n)
      (((n - a : ℕ) : ℝ) * CE / profileScale a ^ 4) := by
  intro j
  rw [densityHigherSegment, truncatedForcingTerm]
  calc
    |∑ s ∈ Finset.Ico a n,
        terminalTransportWeight
            (fun i ↦ transportCoeff m (orbit m p₀ i)) s n *
          (shiftLeft^[n - 1 - s]) (densityE m p₀ s) j| ≤
        ∑ s ∈ Finset.Ico a n,
          |terminalTransportWeight
              (fun i ↦ transportCoeff m (orbit m p₀ i)) s n *
            (shiftLeft^[n - 1 - s]) (densityE m p₀ s) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.Ico a n, CE / profileScale a ^ 4 := by
      apply Finset.sum_le_sum
      intro s hs
      have has : a ≤ s := (Finset.mem_Ico.mp hs).1
      have hweight :
          |terminalTransportWeight
              (fun i ↦ transportCoeff m (orbit m p₀ i)) s n| ≤ 1 := by
        exact abs_transportBetween_orbit_le_one m p₀ hm hcrit (s + 1) n
      have hsource :
          |(shiftLeft^[n - 1 - s]) (densityE m p₀ s) j| ≤
            CE / profileScale s ^ 4 := by
        rw [shiftLeft_iterate_apply]
        exact supLE_of_weightedSupThree
          (profileScale s) (CE / profileScale s ^ 4)
          (profileScale_pos s) (densityE m p₀ s) (hE s)
          (j + (n - 1 - s))
      have hsourceNonneg : 0 ≤ CE / profileScale s ^ 4 :=
        div_nonneg hCE (pow_nonneg (profileScale_pos s).le 4)
      have hterm :
          |terminalTransportWeight
              (fun i ↦ transportCoeff m (orbit m p₀ i)) s n *
            (shiftLeft^[n - 1 - s]) (densityE m p₀ s) j| ≤
            CE / profileScale s ^ 4 := by
        rw [abs_mul]
        calc
          |terminalTransportWeight
                (fun i ↦ transportCoeff m (orbit m p₀ i)) s n| *
              |(shiftLeft^[n - 1 - s]) (densityE m p₀ s) j| ≤
              1 * (CE / profileScale s ^ 4) :=
            mul_le_mul hweight hsource (abs_nonneg _) (by norm_num)
          _ = CE / profileScale s ^ 4 := one_mul _
      have hscale : profileScale a ≤ profileScale s := by
        simpa only [profileScale] using
          (show (((a + 1 : ℕ) : ℕ) : ℝ) ≤ (((s + 1 : ℕ) : ℕ) : ℝ) by
            exact_mod_cast Nat.succ_le_succ has)
      have hcompare : CE / profileScale s ^ 4 ≤ CE / profileScale a ^ 4 :=
        div_le_div_of_nonneg_left hCE (pow_pos (profileScale_pos a) 4)
          (pow_le_pow_left₀ (profileScale_pos a).le hscale 4)
      exact hterm.trans hcompare
    _ = ((n - a : ℕ) : ℝ) * CE / profileScale a ^ 4 := by
      rw [Finset.sum_const, Nat.card_Ico]
      simp only [nsmul_eq_mul]
      ring

/-- Orbit form of the preceding bound, deriving the order-four source estimate
from the weighted mass and pointwise profile bounds. -/
theorem densityHigherSegment_supLE_of_orbit_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / profileScale n)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / profileScale n ^ 2))
    {a n : ℕ} (han : a ≤ n) :
    SupLE (densityHigherSegment m p₀ a n)
      (((n - a : ℕ) : ℝ) * densityEOrbitSupConstant m A B /
        profileScale a ^ 4) := by
  have hCE : 0 ≤ densityEOrbitSupConstant m A B :=
    (densityEOrbitConstants_nonneg m A B hA hB).1
  exact densityHigherSegment_supLE_of_order_four
    m p₀ hm hcrit (densityEOrbitSupConstant m A B) hCE
      (densityE_orbit_weightedSup_order_four
        m p₀ hm hcrit hthird A B hA hB hL1 hSup) han

/-- On a positive macroscopic time annulus, the quadratic rescaling of a
finite higher-source segment is bounded by a constant times the mesh.  This
is the quantitative estimate behind the vanishing assertion in U45. -/
theorem densityHigherSegment_scaled_abs_le_const_div
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (CE : ℝ) (hCE : 0 ≤ CE)
    (hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4))
    (eta T : ℝ) (heta : 0 < eta) (hT : 0 ≤ T)
    (N a n j : ℕ) (hN : 1 ≤ N) (han : a ≤ n)
    (ha : eta * (N : ℝ) ≤ profileScale a)
    (hspan : ((n - a : ℕ) : ℝ) ≤ T * (N : ℝ)) :
    |(N : ℝ) ^ 2 * densityHigherSegment m p₀ a n j| ≤
      (T * CE / eta ^ 4) / (N : ℝ) := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hetaN : 0 < eta * (N : ℝ) := mul_pos heta hNreal
  have hLa : 0 < profileScale a := profileScale_pos a
  have hsegment :=
    densityHigherSegment_supLE_of_order_four
      m p₀ hm hcrit CE hCE hE han j
  have hspanCE :
      ((n - a : ℕ) : ℝ) * CE ≤ (T * (N : ℝ)) * CE :=
    mul_le_mul_of_nonneg_right hspan hCE
  have hnum : 0 ≤ (T * (N : ℝ)) * CE :=
    mul_nonneg (mul_nonneg hT hNreal.le) hCE
  have hpow : (eta * (N : ℝ)) ^ 4 ≤ profileScale a ^ 4 :=
    pow_le_pow_left₀ hetaN.le ha 4
  calc
    |(N : ℝ) ^ 2 * densityHigherSegment m p₀ a n j| =
        (N : ℝ) ^ 2 * |densityHigherSegment m p₀ a n j| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (N : ℝ))]
    _ ≤ (N : ℝ) ^ 2 *
        (((n - a : ℕ) : ℝ) * CE / profileScale a ^ 4) :=
      mul_le_mul_of_nonneg_left hsegment (sq_nonneg (N : ℝ))
    _ ≤ (N : ℝ) ^ 2 *
        ((T * (N : ℝ)) * CE / profileScale a ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (N : ℝ))
      exact div_le_div_of_nonneg_right hspanCE (pow_nonneg hLa.le 4)
    _ ≤ (N : ℝ) ^ 2 *
        ((T * (N : ℝ)) * CE / (eta * (N : ℝ)) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (N : ℝ))
      exact div_le_div_of_nonneg_left hnum (pow_pos hetaN 4) hpow
    _ = (T * CE / eta ^ 4) / (N : ℝ) := by
      field_simp [heta.ne', hNreal.ne']
      ring

/-- Moving-index form of higher-source vanishing.  The start and end indices
may be arbitrary sequences: only a positive lower macroscopic time and an
`O(N)` window length are used. -/
theorem densityHigherSegment_scaled_tendsto_zero_of_order_four_on_annulus
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (CE : ℝ) (hCE : 0 ≤ CE)
    (hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4))
    (eta T : ℝ) (heta : 0 < eta) (hT : 0 ≤ T)
    (a n j : ℕ → ℕ)
    (han : ∀ᶠ N : ℕ in atTop, a N ≤ n N)
    (ha : ∀ᶠ N : ℕ in atTop,
      eta * (N : ℝ) ≤ profileScale (a N))
    (hspan : ∀ᶠ N : ℕ in atTop,
      (((n N - a N : ℕ) : ℕ) : ℝ) ≤ T * (N : ℝ)) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 2 * densityHigherSegment m p₀ (a N) (n N) (j N))
      atTop (𝓝 0) := by
  have herror :
      Tendsto (fun N : ℕ ↦ (T * CE / eta ^ 4) / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (T * CE / eta ^ 4)
  apply tendsto_of_abs_sub_le_error tendsto_const_nhds herror
  filter_upwards [eventually_ge_atTop (1 : ℕ), han, ha, hspan]
    with N hN hAN hscale hwindow
  simpa only [sub_zero] using
    densityHigherSegment_scaled_abs_le_const_div
      m p₀ hm hcrit CE hCE hE eta T heta hT
      N (a N) (n N) (j N) hN hAN hscale hwindow

/-- Source-facing orbit specialization: the order-four estimate is derived
from the actual weighted `L¹` and weighted supremum bounds. -/
theorem densityHigherSegment_orbit_scaled_tendsto_zero_on_annulus
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (eta T : ℝ) (heta : 0 < eta) (hT : 0 ≤ T)
    (a n j : ℕ → ℕ)
    (han : ∀ᶠ N : ℕ in atTop, a N ≤ n N)
    (ha : ∀ᶠ N : ℕ in atTop,
      eta * (N : ℝ) ≤ profileScale (a N))
    (hspan : ∀ᶠ N : ℕ in atTop,
      (((n N - a N : ℕ) : ℕ) : ℝ) ≤ T * (N : ℝ)) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 2 * densityHigherSegment m p₀ (a N) (n N) (j N))
      atTop (𝓝 0) := by
  apply densityHigherSegment_scaled_tendsto_zero_of_order_four_on_annulus
    m p₀ hm hcrit (densityEOrbitSupConstant m A B)
    (densityEOrbitConstants_nonneg m A B hA hB).1
    (densityE_orbit_weightedSup_order_four
      m p₀ hm hcrit hthird A B hA hB hL1 hSup)
    eta T heta hT a n j han ha hspan

end

end DerridaRetaux
