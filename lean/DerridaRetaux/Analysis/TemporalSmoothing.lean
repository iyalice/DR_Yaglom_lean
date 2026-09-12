import DerridaRetaux.Analysis.CoefficientVariation
import DerridaRetaux.Analysis.LogSmoothingArithmetic
import Mathlib.Tactic

/-!
# Temporal smoothing from the exact density recurrence

This file proves the finite-time Duhamel estimate used in `eq:timemod`.  The
argument is split into a generic contraction-with-forcing lemma and an orbit
instantiation.  The pointwise estimate and the spatial modulus remain explicit
upstream premises; the temporal estimate is not assumed.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-- Unweighted pointwise bounds add. -/
theorem supLE_add (f g : Seq) (A B : ℝ) (hf : SupLE f A) (hg : SupLE g B) :
    SupLE (f + g) (A + B) := by
  intro j
  calc
    |(f + g) j| ≤ |f j| + |g j| := abs_add _ _
    _ ≤ A + B := add_le_add (hf j) (hg j)

/-- Unweighted pointwise bounds scale by the absolute scalar. -/
theorem supLE_smul (f : Seq) (A c : ℝ) (hf : SupLE f A) :
    SupLE (c • f) (|c| * A) := by
  intro j
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg c)

/-- A left shift preserves an unweighted pointwise bound. -/
theorem supLE_shiftLeft (f : Seq) (A : ℝ) (hf : SupLE f A) :
    SupLE (shiftLeft f) A := by
  intro j
  exact hf (j + 1)

/-- Every finite iterate of the left shift preserves an unweighted bound. -/
theorem supLE_shiftLeft_iterate (f : Seq) (A : ℝ) (h : ℕ) (hf : SupLE f A) :
    SupLE ((shiftLeft^[h]) f) A := by
  intro j
  rw [shiftLeft_iterate_apply]
  exact hf (j + h)

/-- A weighted cubic pointwise bound controls the ordinary pointwise norm when
the scale is positive. -/
theorem supLE_of_weightedSupThree
    (L A : ℝ) (hL : 0 < L) (f : Seq) (hf : WeightedSupThreeLE L f A) :
    SupLE f A := by
  intro j
  have hj : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hL.le
  have hw : 1 ≤ cubicWeight L j := by
    unfold cubicWeight
    nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) ≤ 1 + (j : ℝ) / L by linarith) 3]
  calc
    |f j| ≤ cubicWeight L j * |f j| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (abs_nonneg (f j))
    _ ≤ A := hf j

/-- The nonlinear part of the short density recursion. -/
def densityFullSource (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  densityD m p₀ s • densityB m p₀ s + densityE m p₀ s

/-- Exact one-step form `rho_(s+1) = c_s S rho_s + source_s`. -/
theorem positiveTiltedDensity_orbit_succ_fullSource
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (s + 1)) =
      transportCoeff m (orbit m p₀ s) •
          shiftLeft (positiveTiltedDensity m (orbit m p₀ s)) +
        densityFullSource m p₀ s := by
  rw [positiveTiltedDensity_orbit_succ_short m p₀ hm hcrit s]
  funext j
  simp only [shortDensityStep, densityFullSource, densityB, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- A generic finite-time Duhamel estimate.  Only contraction of the transport,
uniform coefficient defect, and a uniform forcing bound are used. -/
theorem supLE_iterate_recurrence_sub_shift
    (u : ℕ → Seq) (c : ℕ → ℝ) (forcing : ℕ → Seq)
    (n h : ℕ) (B D E : ℝ)
    (hD : 0 ≤ D)
    (hrec : ∀ s : ℕ,
      u (s + 1) = c s • shiftLeft (u s) + forcing s)
    (hc : ∀ i : ℕ, i < h → |c (n + i)| ≤ 1)
    (hdefect : ∀ i : ℕ, i < h → |c (n + i) - 1| ≤ D)
    (hu : SupLE (u n) B)
    (hforcing : ∀ i : ℕ, i < h → SupLE (forcing (n + i)) E) :
    SupLE (u (n + h) - (shiftLeft^[h]) (u n))
      ((h : ℝ) * (D * B + E)) := by
  induction h with
  | zero =>
      intro j
      simp
  | succ h ih =>
      have hcPrev : ∀ i : ℕ, i < h → |c (n + i)| ≤ 1 :=
        fun i hi ↦ hc i (hi.trans (Nat.lt_succ_self h))
      have hdPrev : ∀ i : ℕ, i < h → |c (n + i) - 1| ≤ D :=
        fun i hi ↦ hdefect i (hi.trans (Nat.lt_succ_self h))
      have hfPrev : ∀ i : ℕ, i < h → SupLE (forcing (n + i)) E :=
        fun i hi ↦ hforcing i (hi.trans (Nat.lt_succ_self h))
      have hih := ih hcPrev hdPrev hfPrev
      have hcLast := hc h (Nat.lt_succ_self h)
      have hdLast := hdefect h (Nat.lt_succ_self h)
      have hfLast := hforcing h (Nat.lt_succ_self h)
      intro j
      have hindex : n + (h + 1) = (n + h) + 1 := by omega
      rw [hindex, hrec (n + h)]
      simp only [Function.iterate_succ_apply', Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, shiftLeft_apply]
      have hdecomp :
          c (n + h) * u (n + h) (j + 1) + forcing (n + h) j -
              (shiftLeft^[h]) (u n) (j + 1) =
            c (n + h) *
                (u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1)) +
              (c (n + h) - 1) * (shiftLeft^[h]) (u n) (j + 1) +
              forcing (n + h) j := by
        ring
      rw [hdecomp]
      calc
        |c (n + h) *
              (u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1)) +
            (c (n + h) - 1) * (shiftLeft^[h]) (u n) (j + 1) +
            forcing (n + h) j| ≤
            |c (n + h)| *
                |u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1)| +
              |c (n + h) - 1| * |(shiftLeft^[h]) (u n) (j + 1)| +
              |forcing (n + h) j| := by
          calc
            |c (n + h) *
                  (u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1)) +
                (c (n + h) - 1) * (shiftLeft^[h]) (u n) (j + 1) +
                forcing (n + h) j| ≤
                |c (n + h) *
                    (u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1))| +
                  |(c (n + h) - 1) * (shiftLeft^[h]) (u n) (j + 1)| +
                  |forcing (n + h) j| := by
              exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
            _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ 1 * ((h : ℝ) * (D * B + E)) + D * B + E := by
          have hfirst :
              |c (n + h)| *
                  |u (n + h) (j + 1) - (shiftLeft^[h]) (u n) (j + 1)| ≤
                1 * ((h : ℝ) * (D * B + E)) := by
            exact mul_le_mul hcLast (hih (j + 1)) (abs_nonneg _)
              (by norm_num)
          have hsecond :
              |c (n + h) - 1| * |(shiftLeft^[h]) (u n) (j + 1)| ≤ D * B := by
            exact mul_le_mul hdLast
              (supLE_shiftLeft_iterate (u n) B h hu (j + 1))
              (abs_nonneg _) hD
          exact add_le_add (add_le_add hfirst hsecond) (hfLast j)
        _ = (((h + 1 : ℕ) : ℝ) * (D * B + E)) := by
          push_cast
          ring

/-- The full density source has order `L_s^-3` under the weighted-mass and
pointwise inputs. -/
theorem densityFullSource_orbit_weightedSup_order_three
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤ A / profileScale n)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / profileScale n ^ 2)) (s : ℕ) :
    WeightedSupThreeLE (profileScale s) (densityFullSource m p₀ s)
      (((Nat.choose m 2 : ℝ) * B * A + densityEOrbitSupConstant m A B) /
        profileScale s ^ 3) := by
  let L := profileScale s
  let D : ℝ := Nat.choose m 2
  let CE := densityEOrbitSupConstant m A B
  have hL : 1 ≤ L := by
    dsimp [L, profileScale]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hconv :=
    (weightedConvolutionPowers_orbit_bounds
      m p₀ hm hcrit hthird A B hA hB hL1 hSup s 1).2
  have hd := (smoothing_coefficients_orbit_bounds m p₀ hm hcrit s).2
  have hdB : WeightedSupThreeLE L (densityD m p₀ s • densityB m p₀ s)
      (D * (B / L ^ 2 * (A / L))) := by
    apply weightedSupThree_mono L
      (|densityD m p₀ s| * (B / L ^ 2 * (A / L))) _ _
    · exact weightedSupThree_smul L (B / L ^ 2 * (A / L))
        (densityD m p₀ s) (densityB m p₀ s) (by
          simpa [L, profileScale, densityB, convPow_two_eq] using hconv)
    · exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hdB' : WeightedSupThreeLE L (densityD m p₀ s • densityB m p₀ s)
      (D * B * A / L ^ 3) := by
    convert hdB using 1
    field_simp
    ring
  have hE0 := densityE_orbit_weightedSup_order_four
    m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  have hCE : 0 ≤ CE := by
    dsimp [CE]
    exact (densityEOrbitConstants_nonneg m A B hA hB).1
  have hE : WeightedSupThreeLE L (densityE m p₀ s) (CE / L ^ 3) :=
    weightedSupThree_mono L (CE / L ^ 4) (CE / L ^ 3)
      (densityE m p₀ s) (by simpa only [L, CE] using hE0)
      (div_pow_le_div_pow_of_exponent_le CE L 3 4 hCE hL (by omega))
  have hadd := weightedSupThree_add L (D * B * A / L ^ 3) (CE / L ^ 3)
    hLpos (densityD m p₀ s • densityB m p₀ s) (densityE m p₀ s) hdB' hE
  simpa only [densityFullSource, L, D, CE, add_div] using hadd

/-- Iterating the exact orbit recurrence gives the transport error
`rho_(n+h)-S^h rho_n = O(h L_n^-3)`. -/
theorem positiveTiltedDensity_temporalTransport_of_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL1 : ∀ n : ℕ,
      weightedL1Three (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤ A / profileScale n)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / profileScale n ^ 2))
    (hCoeff : ∀ s : ℕ,
      |1 - transportCoeff m (orbit m p₀ s)| ≤ D / profileScale s ^ 2)
    (n h : ℕ) :
    SupLE
      (positiveTiltedDensity m (orbit m p₀ (n + h)) -
        (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
      ((h : ℝ) *
        ((D * B + (Nat.choose m 2 : ℝ) * B * A +
            densityEOrbitSupConstant m A B) / profileScale n ^ 3)) := by
  let rho : ℕ → Seq := fun s ↦ positiveTiltedDensity m (orbit m p₀ s)
  let c : ℕ → ℝ := fun s ↦ transportCoeff m (orbit m p₀ s)
  let forcing : ℕ → Seq := fun s ↦ densityFullSource m p₀ s
  let CS : ℝ := (Nat.choose m 2 : ℝ) * B * A + densityEOrbitSupConstant m A B
  have hCS : 0 ≤ CS := by
    dsimp [CS]
    exact add_nonneg (by positivity)
      (densityEOrbitConstants_nonneg m A B hA hB).1
  have hLn : 0 < profileScale n := profileScale_pos n
  have hLnOne : 1 ≤ profileScale n := by
    dsimp [profileScale]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hrec : ∀ s : ℕ, rho (s + 1) = c s • shiftLeft (rho s) + forcing s := by
    intro s
    exact positiveTiltedDensity_orbit_succ_fullSource m p₀ hm hcrit s
  have hc : ∀ i : ℕ, i < h → |c (n + i)| ≤ 1 := by
    intro i hi
    exact (smoothing_coefficients_orbit_bounds m p₀ hm hcrit (n + i)).1
  have hdefect : ∀ i : ℕ, i < h →
      |c (n + i) - 1| ≤ D / profileScale n ^ 2 := by
    intro i hi
    have hraw := hCoeff (n + i)
    rw [abs_sub_comm] at hraw
    have hscale : profileScale n ≤ profileScale (n + i) := by
      simp only [profileScale]
      exact_mod_cast (show n + 1 ≤ n + i + 1 by omega)
    calc
      |c (n + i) - 1| ≤ D / profileScale (n + i) ^ 2 := hraw
      _ ≤ D / profileScale n ^ 2 := by
        exact div_le_div_of_nonneg_left hD (pow_pos hLn 2)
          (pow_le_pow_left₀ hLn.le hscale 2)
  have hu : SupLE (rho n) (B / profileScale n ^ 2) :=
    supLE_of_weightedSupThree (profileScale n) _ hLn (rho n) (hSup n)
  have hforcing : ∀ i : ℕ, i < h →
      SupLE (forcing (n + i)) (CS / profileScale n ^ 3) := by
    intro i hi
    have hs := densityFullSource_orbit_weightedSup_order_three
      m p₀ hm hcrit hthird A B hA hB hL1 hSup (n + i)
    have hsUnweighted : SupLE (forcing (n + i))
        (CS / profileScale (n + i) ^ 3) := by
      exact supLE_of_weightedSupThree (profileScale (n + i)) _
        (profileScale_pos (n + i)) (forcing (n + i)) (by
          simpa only [forcing, CS] using hs)
    intro j
    calc
      |forcing (n + i) j| ≤ CS / profileScale (n + i) ^ 3 := hsUnweighted j
      _ ≤ CS / profileScale n ^ 3 := by
        have hscale : profileScale n ≤ profileScale (n + i) := by
          simp only [profileScale]
          exact_mod_cast (show n + 1 ≤ n + i + 1 by omega)
        exact div_le_div_of_nonneg_left hCS (pow_pos hLn 3)
          (pow_le_pow_left₀ hLn.le hscale 3)
  have hgeneric := supLE_iterate_recurrence_sub_shift rho c forcing n h
    (B / profileScale n ^ 2) (D / profileScale n ^ 2)
    (CS / profileScale n ^ 3)
    (div_nonneg hD (sq_nonneg _)) hrec hc hdefect hu hforcing
  apply fun j ↦ (hgeneric j).trans ?_
  have hDB : 0 ≤ D * B := mul_nonneg hD hB
  have hcompare : D * B / profileScale n ^ 4 ≤ D * B / profileScale n ^ 3 :=
    div_pow_le_div_pow_of_exponent_le (D * B) (profileScale n) 3 4
      hDB hLnOne (by omega)
  have hinner :
      (D / profileScale n ^ 2) * (B / profileScale n ^ 2) +
          CS / profileScale n ^ 3 ≤
        (D * B + CS) / profileScale n ^ 3 := by
    calc
      (D / profileScale n ^ 2) * (B / profileScale n ^ 2) +
          CS / profileScale n ^ 3 =
          D * B / profileScale n ^ 4 + CS / profileScale n ^ 3 := by
            congr 1
            rw [div_mul_div_comm]
            congr 1
            ring
      _ ≤ D * B / profileScale n ^ 3 + CS / profileScale n ^ 3 :=
        add_le_add_right hcompare _
      _ = (D * B + CS) / profileScale n ^ 3 := by ring
  calc
    (h : ℝ) *
        ((D / profileScale n ^ 2) * (B / profileScale n ^ 2) +
          CS / profileScale n ^ 3) ≤
      (h : ℝ) * ((D * B + CS) / profileScale n ^ 3) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg h)
    _ = (h : ℝ) *
        ((D * B + (Nat.choose m 2 : ℝ) * B * A +
          densityEOrbitSupConstant m A B) / profileScale n ^ 3) := by
      dsimp [CS]
      ring

/-- The source-shaped temporal modulus follows by combining the temporal
transport estimate with the already established spatial modulus. -/
theorem positiveTiltedDensity_temporalModulus_of_spatial
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B D S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL1 : ∀ n : ℕ,
      weightedL1Three (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤ A / profileScale n)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / profileScale n ^ 2))
    (hCoeff : ∀ s : ℕ,
      |1 - transportCoeff m (orbit m p₀ s)| ≤ D / profileScale s ^ 2)
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (S * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))))
    (n h : ℕ) (hh : 1 ≤ h) (hhL : h ≤ n + 1) :
    SupLE
      (positiveTiltedDensity m (orbit m p₀ (n + h)) -
        positiveTiltedDensity m (orbit m p₀ n))
      ((D * B + (Nat.choose m 2 : ℝ) * B * A +
          densityEOrbitSupConstant m A B + S) *
        (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) := by
  let rhoN := positiveTiltedDensity m (orbit m p₀ n)
  let CT := D * B + (Nat.choose m 2 : ℝ) * B * A +
    densityEOrbitSupConstant m A B
  have hCT : 0 ≤ CT := by
    dsimp [CT]
    have hCE := (densityEOrbitConstants_nonneg m A B hA hB).1
    positivity
  have htransport := positiveTiltedDensity_temporalTransport_of_bounds
    m p₀ hm hcrit hthird A B D hA hB hD hL1 hSup hCoeff n h
  have hspatialW := hSpatial n h hh hhL
  have hspatial : SupLE (rhoN - (shiftLeft^[h]) rhoN)
      (S * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ)))) :=
    supLE_of_weightedSupThree (profileScale n) _ (profileScale_pos n) _ hspatialW
  have hhPos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hh
  have hratio : 1 ≤ profileScale n / (h : ℝ) := by
    apply (le_div_iff₀ hhPos).2
    simpa only [one_mul, profileScale] using
      (show ((h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by
      exact_mod_cast hhL)
  have hlog : 1 ≤ 1 + Real.log (profileScale n / (h : ℝ)) := by
    linarith [Real.log_nonneg hratio]
  intro j
  have hdecomp :
      positiveTiltedDensity m (orbit m p₀ (n + h)) j - rhoN j =
        (positiveTiltedDensity m (orbit m p₀ (n + h)) j -
          (shiftLeft^[h]) rhoN j) -
        (rhoN j - (shiftLeft^[h]) rhoN j) := by ring
  rw [Pi.sub_apply, hdecomp]
  calc
    |positiveTiltedDensity m (orbit m p₀ (n + h)) j -
        (shiftLeft^[h]) rhoN j -
        (rhoN j - (shiftLeft^[h]) rhoN j)| ≤
      |positiveTiltedDensity m (orbit m p₀ (n + h)) j -
        (shiftLeft^[h]) rhoN j| + |rhoN j - (shiftLeft^[h]) rhoN j| :=
      abs_sub _ _
    _ ≤ (h : ℝ) * (CT / profileScale n ^ 3) +
        S * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) :=
      add_le_add (by simpa only [rhoN, CT] using htransport j) (hspatial j)
    _ ≤ CT * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) +
        S * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) := by
      exact add_le_add_right (by
        calc
          (h : ℝ) * (CT / profileScale n ^ 3) =
              CT * (h : ℝ) / profileScale n ^ 3 := by ring
          _ ≤ CT * (h : ℝ) / profileScale n ^ 3 *
              (1 + Real.log (profileScale n / (h : ℝ))) :=
            by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hlog
                (show 0 ≤ CT * (h : ℝ) / profileScale n ^ 3 by
                  exact div_nonneg (mul_nonneg hCT (Nat.cast_nonneg h))
                    (pow_nonneg (profileScale_pos n).le 3)))) _
    _ = (CT + S) * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) := by ring
    _ = _ := by rfl

/-- Orbit-level `eq:timemod`: H1a/H1b provide the coefficient and weighted-mass
bounds, while `eq:sup` and the already proved spatial modulus are the only explicit
internal premises.  No temporal modulus is assumed. -/
theorem positiveTiltedDensity_temporalModulus_of_H1_and_spatial
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (B S : ℝ) (hS : 0 ≤ S)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / profileScale n ^ 2))
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (S * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (C * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) := by
  have hB : 0 ≤ B := by
    have hzero := hSup 0 0
    have habs : |positiveTiltedDensity m (orbit m p₀ 0) 0| ≤ B := by
      simpa [profileScale, cubicWeight] using hzero
    exact (abs_nonneg _).trans habs
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨A, hA, hL1⟩
  rcases coefficientVariation_orbit_of_H1a_and_pointwise
      m p₀ hm hcrit hthird hnonconstant hExcess B hSup with
    ⟨D, hD, _hmass, _hx, _hd, hCoeff, _hxVariation, _hdVariation⟩
  let Base : ℝ := D * B + (Nat.choose m 2 : ℝ) * B * A +
    densityEOrbitSupConstant m A B + S
  let C : ℝ := Base + 1
  have hBase : 0 ≤ Base := by
    dsimp [Base]
    have hCE := (densityEOrbitConstants_nonneg m A B hA.le hB).1
    positivity
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro n h hh hhL
  have hraw := positiveTiltedDensity_temporalModulus_of_spatial
    m p₀ hm hcrit hthird A B D S hA.le hB hD.le
    (by simpa only [profileScale] using hL1) hSup
    (by simpa only [profileScale] using hCoeff) hSpatial n h hh hhL
  intro j
  apply (hraw j).trans
  have hhPos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hh
  have hratio : 1 ≤ profileScale n / (h : ℝ) := by
    apply (le_div_iff₀ hhPos).2
    simpa only [one_mul, profileScale] using
      (show ((h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast hhL)
  have hfactor :
      0 ≤ (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ))) := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg h) (pow_nonneg (profileScale_pos n).le 3))
      (by linarith [Real.log_nonneg hratio])
  have hBaseC :
      D * B + (Nat.choose m 2 : ℝ) * B * A +
          densityEOrbitSupConstant m A B + S ≤ C := by
    dsimp [C, Base]
    linarith
  calc
    (D * B + (Nat.choose m 2 : ℝ) * B * A +
        densityEOrbitSupConstant m A B + S) *
          (h : ℝ) / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / (h : ℝ))) =
      (D * B + (Nat.choose m 2 : ℝ) * B * A +
        densityEOrbitSupConstant m A B + S) *
          ((h : ℝ) / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / (h : ℝ)))) := by ring
    _ ≤ C * ((h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) :=
      mul_le_mul_of_nonneg_right hBaseC hfactor
    _ = C * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) := by ring

end

end DerridaRetaux
