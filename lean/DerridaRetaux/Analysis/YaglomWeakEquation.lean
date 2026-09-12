import DerridaRetaux.Analysis.WeakIntegratedIdentity
import Mathlib.Analysis.Convolution
import DerridaRetaux.Analysis.LaplaceUniqueness
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory Set Filter Topology

namespace DerridaRetaux

noncomputable section

/-- Time derivative of the explicit Yaglom density. -/
lemma yaglomDensity_hasDerivAt_time (t x : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s ↦ yaglomDensity s x)
      ((-8 / t ^ 3 + 8 * x / t ^ 4) * Real.exp (-2 * x / t)) t := by
  unfold yaglomDensity
  convert (hasDerivAt_const t 4).div
    (((hasDerivAt_id t).pow 2)) (pow_ne_zero 2 ht) |>.mul
      (Real.hasDerivAt_exp (-2 * x / t) |>.comp t
        ((hasDerivAt_const t (-2 * x)).div (hasDerivAt_id t) ht)) using 1 <;>
    field_simp <;> ring

/-- Spatial derivative of the explicit Yaglom density. -/
lemma yaglomDensity_hasDerivAt_space (t x : ℝ) (ht : t ≠ 0) :
    HasDerivAt (yaglomDensity t)
      ((-8 / t ^ 3) * Real.exp (-2 * x / t)) x := by
  unfold yaglomDensity
  convert (hasDerivAt_const x (4 / t ^ 2)).mul
    (Real.hasDerivAt_exp (-2 * x / t) |>.comp x
      ((hasDerivAt_const x (-2)).mul (hasDerivAt_id x) |>.div_const t)) using 1 <;>
    field_simp <;> ring

/-- The explicit Yaglom density is closed under positive self-convolution. -/
lemma positiveSelfConvolution_yaglomDensity (t x : ℝ) (ht : t ≠ 0) (hx : 0 ≤ x) :
    positiveSelfConvolution (yaglomDensity t) x =
      (16 * x / t ^ 4) * Real.exp (-2 * x / t) := by
  unfold positiveSelfConvolution
  have hfun : (fun y : ℝ ↦ yaglomDensity t y * yaglomDensity t (x - y)) =
      fun _ : ℝ ↦ (16 / t ^ 4) * Real.exp (-2 * x / t) := by
    funext y
    unfold yaglomDensity
    calc
      4 / t ^ 2 * Real.exp (-2 * y / t) *
          (4 / t ^ 2 * Real.exp (-2 * (x - y) / t)) =
          (16 / t ^ 4) *
            (Real.exp (-2 * y / t) * Real.exp (-2 * (x - y) / t)) := by ring
      _ = (16 / t ^ 4) * Real.exp (-2 * x / t) := by
        rw [← Real.exp_add]
        congr 2
        field_simp [ht]
        ring
  rw [hfun, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp [ht]
  ring


/-- Fubini and translation identify the literal double integral with convolution pairing. -/
theorem weakQuadraticPairing_eq_integral_positiveSelfConvolution
    (phi u : ℝ → ℝ) (hphi : Continuous phi)
    (hcompact : HasCompactSupport phi)
    (hu : IntegrableOn u (Ici (0 : ℝ))) :
    weakQuadraticPairing phi u =
      ∫ z in Ici (0 : ℝ), phi z * positiveSelfConvolution u z := by
  let f : ℝ → ℝ := (Ioi (0 : ℝ)).indicator u
  have hf : Integrable f := by
    change Integrable ((Ioi (0 : ℝ)).indicator u)
    exact (integrable_indicator_iff measurableSet_Ioi).2
      (hu.mono_set Ioi_subset_Ici_self)
  have hkernel : Integrable
      (fun p : ℝ × ℝ ↦ f p.2 * f (p.1 - p.2)) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      MeasureTheory.Integrable.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ) hf hf
  have hRange := (hcompact.isCompact_range hphi).isBounded
  rw [isBounded_iff_forall_norm_le] at hRange
  obtain ⟨C, hC⟩ := hRange
  have hBound : ∀ z : ℝ, ‖phi z‖ ≤ C := fun z ↦ hC (phi z) ⟨z, rfl⟩
  have hPhiMeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ phi p.1) :=
    (hphi.measurable.comp measurable_fst).aestronglyMeasurable
  have hK : Integrable
      (fun p : ℝ × ℝ ↦ phi p.1 * (f p.2 * f (p.1 - p.2))) :=
    hkernel.bdd_mul hPhiMeas ⟨C, fun p ↦ hBound p.1⟩
  unfold weakQuadraticPairing
  rw [integral_Ici_eq_integral_Ioi]
  conv_lhs => enter [2, x]; rw [integral_Ici_eq_integral_Ioi]
  rw [integral_Ici_eq_integral_Ioi]
  calc
    (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), phi (x + y) * u x * u y) =
        ∫ x : ℝ, ∫ y : ℝ, phi (x + y) * f x * f y := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y ∈ Ioi (0 : ℝ)
        · simp only [f, indicator_of_mem hx, indicator_of_mem hy]
        · simp [f, hy]
      · simp [f, hx]
    _ = ∫ x : ℝ, ∫ z : ℝ, phi z * (f x * f (z - x)) := by
      apply integral_congr_ae
      filter_upwards with x
      have htranslate := integral_add_right_eq_self (μ := volume)
        (fun z : ℝ ↦ phi z * (f x * f (z - x))) x
      convert htranslate using 1
      apply integral_congr_ae
      filter_upwards with y
      ring_nf
    _ = ∫ z : ℝ, ∫ x : ℝ, phi z * (f x * f (z - x)) := by
      exact (integral_integral_swap hK).symm
    _ = ∫ z in Ioi (0 : ℝ), phi z * positiveSelfConvolution u z := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hz, integral_mul_left]
        congr 1
        unfold positiveSelfConvolution
        rw [intervalIntegral.integral_of_le hz.le,
          integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioo (0 : ℝ) z
        · simp [f, hx.1, sub_pos.mpr hx.2, hx]
        · rcases not_and_or.mp hx with hx0 | hxz
          · rw [show f x = 0 by
                dsimp only [f]
                exact indicator_of_not_mem (not_mem_Ioi.mpr (le_of_not_gt hx0)) u,
              indicator_of_not_mem hx, zero_mul]
          · rw [show f (z - x) = 0 by
                dsimp only [f]
                exact indicator_of_not_mem
                  (not_mem_Ioi.mpr (sub_nonpos.mpr (le_of_not_gt hxz))) u,
              indicator_of_not_mem hx, mul_zero]
      · rw [indicator_of_not_mem hz]
        have hzle : z ≤ 0 := le_of_not_gt hz
        have hzero : (fun x : ℝ ↦ f x * f (z - x)) = 0 := by
          funext x
          by_cases hx : 0 < x
          · have hzx : z - x ≤ 0 := by linarith
            rw [show f (z - x) = 0 by
              dsimp only [f]
              exact indicator_of_not_mem (not_mem_Ioi.mpr hzx) u]
            simp
          · rw [show f x = 0 by
              dsimp only [f]
              exact indicator_of_not_mem (not_mem_Ioi.mpr (le_of_not_gt hx)) u]
            simp
        have hintegrand : (fun x : ℝ ↦ phi z * (f x * f (z - x))) = 0 := by
          funext x
          rw [congrFun hzero x]
          simp
        simpa only [hintegrand] using (integral_zero ℝ ℝ)

/-- Integration by parts exposes the boundary trace at the origin. -/
theorem yaglomDensity_transport_integration_by_parts
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (t : ℝ) (ht : 0 < t) :
    (∫ x in Ici (0 : ℝ),
        phi x * ((-8 / t ^ 3) * Real.exp (-2 * x / t))) =
      -phi 0 * yaglomDensity t 0 -
        ∫ x in Ici (0 : ℝ), deriv phi x * yaglomDensity t x := by
  let v' : ℝ → ℝ := fun x ↦ (-8 / t ^ 3) * Real.exp (-2 * x / t)
  have hv'cont : Continuous v' := by
    dsimp only [v']
    fun_prop
  have huv' : Integrable (phi * v') :=
    (hphi.continuous.mul hv'cont).integrable_of_hasCompactSupport hcompact.mul_right
  have hu'v : Integrable (deriv phi * yaglomDensity t) :=
    ((hphi.continuous_deriv (by norm_num)).mul (continuous_yaglomDensity t))
      |>.integrable_of_hasCompactSupport hcompact.deriv.mul_right
  have hzero : Tendsto (phi * yaglomDensity t)
      (𝓝[>] (0 : ℝ)) (𝓝 (phi 0 * yaglomDensity t 0)) :=
    ((hphi.continuous.mul (continuous_yaglomDensity t)).continuousAt)
      |>.mono_left inf_le_left
  have hinfty : Tendsto (phi * yaglomDensity t) atTop (𝓝 0) := by
    have hp : HasCompactSupport (phi * yaglomDensity t) := hcompact.mul_right
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hp
    exact (hp.filter_mono atTop_le_cocompact).tendsto
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := phi 0 * yaglomDensity t 0) (b' := 0)
    (u := phi) (v := yaglomDensity t) (u' := deriv phi) (v' := v')
    (fun x _ ↦ (hphi.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ ↦ yaglomDensity_hasDerivAt_space t x ht.ne')
    huv'.integrableOn hu'v.integrableOn hzero hinfty
  rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  simpa only [v', Pi.mul_apply, zero_sub, neg_mul] using hip

/-- Differentiate the tested explicit density under the integral sign. -/
theorem yaglomDensity_weakObservable_hasDerivAt_raw
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (weakObservable (fun s ↦ yaglomDensity s) phi)
      (∫ x in Ici (0 : ℝ),
        phi x * ((-8 / t ^ 3 + 8 * x / t ^ 4) * Real.exp (-2 * x / t))) t := by
  let D : ℝ → ℝ → ℝ := fun s x ↦
    (-8 / s ^ 3 + 8 * x / s ^ 4) * Real.exp (-2 * x / s)
  let eps : ℝ := t / 2
  have heps : 0 < eps := by dsimp only [eps]; positivity
  let K : Set (ℝ × ℝ) := Metric.closedBall t eps ×ˢ tsupport phi
  have hKcompact : IsCompact K := (isCompact_closedBall t eps).prod hcompact
  have hDcont : ContinuousOn (fun p : ℝ × ℝ ↦ ‖D p.1 p.2‖) K := by
    intro p hp
    have hsball : dist p.1 t ≤ eps := (Metric.mem_closedBall.mp hp.1)
    rw [Real.dist_eq] at hsball
    have hspos : 0 < p.1 := by
      have hlower := (abs_le.mp hsball).1
      dsimp only [eps] at hlower
      linarith
    apply ContinuousAt.continuousWithinAt
    dsimp only [D]
    have hsne : p.1 ≠ 0 := hspos.ne'
    have hfst : ContinuousAt (fun q : ℝ × ℝ ↦ q.1) p := continuous_fst.continuousAt
    have hsnd : ContinuousAt (fun q : ℝ × ℝ ↦ q.2) p := continuous_snd.continuousAt
    have hfirst : ContinuousAt (fun q : ℝ × ℝ ↦ -8 / q.1 ^ 3) p :=
      continuousAt_const.div (hfst.pow 3) (pow_ne_zero 3 hsne)
    have hsecond : ContinuousAt (fun q : ℝ × ℝ ↦ 8 * q.2 / q.1 ^ 4) p :=
      (continuousAt_const.mul hsnd).div (hfst.pow 4) (pow_ne_zero 4 hsne)
    have harg : ContinuousAt (fun q : ℝ × ℝ ↦ -2 * q.2 / q.1) p :=
      (continuousAt_const.mul hsnd).div hfst hsne
    have hexp : ContinuousAt
        (fun q : ℝ × ℝ ↦ Real.exp (-2 * q.2 / q.1)) p := by
      simpa only [Function.comp_apply] using
        Real.continuous_exp.continuousAt.comp harg
    exact ((hfirst.add hsecond).mul hexp).norm
  have hDimage := (hKcompact.image_of_continuousOn hDcont).isBounded
  rw [isBounded_iff_forall_norm_le] at hDimage
  obtain ⟨C₀, hC₀⟩ := hDimage
  let C : ℝ := max C₀ 0
  have hDbound : ∀ p ∈ K, ‖D p.1 p.2‖ ≤ C := by
    intro p hp
    have himage : ‖D p.1 p.2‖ ∈ (fun q : ℝ × ℝ ↦ ‖D q.1 q.2‖) '' K :=
      ⟨p, hp, rfl⟩
    have hb := hC₀ ‖D p.1 p.2‖ himage
    have habs : ‖‖D p.1 p.2‖‖ = ‖D p.1 p.2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [habs] at hb
    exact hb.trans (le_max_left _ _)
  have hphiInt : Integrable phi :=
    hphi.continuous.integrable_of_hasCompactSupport hcompact
  have hboundInt : Integrable (fun x : ℝ ↦ C * ‖phi x‖) :=
    hphiInt.norm.const_mul C
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x : ℝ ↦ phi x * yaglomDensity s x)
        (volume.restrict (Ici (0 : ℝ))) := by
    filter_upwards with s
    exact ((hphi.continuous.mul (continuous_yaglomDensity s)).aestronglyMeasurable)
      |>.mono_measure Measure.restrict_le_self
  have hFint : Integrable
      (fun x : ℝ ↦ phi x * yaglomDensity t x)
      (volume.restrict (Ici (0 : ℝ))) := by
    exact ((hphi.continuous.mul (continuous_yaglomDensity t))
      |>.integrable_of_hasCompactSupport hcompact.mul_right).integrableOn
  have hF'meas : AEStronglyMeasurable
      (fun x : ℝ ↦ phi x * D t x)
      (volume.restrict (Ici (0 : ℝ))) := by
    have hDfixed : Continuous (D t) := by
      dsimp only [D]
      have htne : t ≠ 0 := ht.ne'
      fun_prop
    exact ((hphi.continuous.mul hDfixed).aestronglyMeasurable)
      |>.mono_measure Measure.restrict_le_self
  have hbound : ∀ᵐ x ∂(volume.restrict (Ici (0 : ℝ))),
      ∀ s ∈ Metric.ball t eps, ‖phi x * D s x‖ ≤ C * ‖phi x‖ := by
    filter_upwards with x
    intro s hs
    by_cases hx : x ∈ tsupport phi
    · have hsclosed : s ∈ Metric.closedBall t eps :=
        Metric.ball_subset_closedBall hs
      calc
        ‖phi x * D s x‖ = ‖phi x‖ * ‖D s x‖ := norm_mul _ _
        _ ≤ ‖phi x‖ * C := mul_le_mul_of_nonneg_left
          (hDbound (s, x) ⟨hsclosed, hx⟩) (norm_nonneg _)
        _ = C * ‖phi x‖ := mul_comm _ _
    · have hnot : x ∉ Function.support phi :=
        fun hsupp ↦ hx (subset_closure hsupp)
      have hphizero : phi x = 0 := by
        simpa [Function.mem_support] using hnot
      simp only [hphizero, zero_mul, norm_zero]
      simp [hphizero]
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ici (0 : ℝ))),
      ∀ s ∈ Metric.ball t eps,
        HasDerivAt (fun r ↦ phi x * yaglomDensity r x) (phi x * D s x) s := by
    filter_upwards with x
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hspos : 0 < s := by
      have hlower := (abs_lt.mp hs).1
      dsimp only [eps] at hlower
      linarith
    simpa only [D, zero_mul, zero_add] using
      (hasDerivAt_const s (phi x)).mul (yaglomDensity_hasDerivAt_time s x hspos.ne')
  have hraw := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ici (0 : ℝ))) heps hFmeas hFint hF'meas
    hbound hboundInt.integrableOn hdiff
  simpa only [weakObservable, halfLineTestPairing, D] using hraw.2

/-- The explicit density satisfies the pointwise weak generator identity. -/
theorem yaglomDensity_weakObservable_hasDerivAt
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (weakObservable (fun s ↦ yaglomDensity s) phi)
      (weakEquationRhs (fun s ↦ yaglomDensity s) phi t) t := by
  have hraw := yaglomDensity_weakObservable_hasDerivAt_raw phi hphi hcompact t ht
  apply hraw.congr_deriv
  have hspaceInt : Integrable
      (fun x : ℝ ↦ phi x * ((-8 / t ^ 3) * Real.exp (-2 * x / t))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hphi.continuous.mul (by fun_prop)
    · exact hcompact.mul_right
  have hquadExplicit : Integrable
      (fun x : ℝ ↦ phi x * ((16 * x / t ^ 4) * Real.exp (-2 * x / t))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hphi.continuous.mul (by fun_prop)
    · exact hcompact.mul_right
  have hquadInt : Integrable
      (fun x : ℝ ↦ phi x * positiveSelfConvolution (yaglomDensity t) x)
      (volume.restrict (Ici (0 : ℝ))) := by
    apply hquadExplicit.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [positiveSelfConvolution_yaglomDensity t x ht.ne' hx]
  have hsplit :
      (∫ x in Ici (0 : ℝ),
        phi x * ((-8 / t ^ 3 + 8 * x / t ^ 4) * Real.exp (-2 * x / t))) =
        (∫ x in Ici (0 : ℝ),
          phi x * ((-8 / t ^ 3) * Real.exp (-2 * x / t))) +
        (1 / 2 : ℝ) * ∫ x in Ici (0 : ℝ),
          phi x * positiveSelfConvolution (yaglomDensity t) x := by
    rw [← integral_const_mul]
    rw [← integral_add hspaceInt.integrableOn (hquadInt.const_mul (1 / 2))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [positiveSelfConvolution_yaglomDensity t x ht.ne' hx]
    ring
  rw [hsplit, yaglomDensity_transport_integration_by_parts phi hphi hcompact t ht,
    ← weakQuadraticPairing_eq_integral_positiveSelfConvolution phi (yaglomDensity t) hphi.continuous hcompact
      (integrableOn_yaglomDensity ht)]
  rfl

/-- A continuous two-observable formula for the explicit weak generator. -/
theorem weakEquationRhs_yaglomDensity_eq_combo
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (t : ℝ) (ht : 0 < t) :
    weakEquationRhs (fun s ↦ yaglomDensity s) phi t =
      (-2 / t) * weakObservable (fun s ↦ yaglomDensity s) phi t +
      (2 / t ^ 2) * weakObservable (fun s ↦ yaglomDensity s)
        (fun x ↦ x * phi x) t := by
  have hweak := yaglomDensity_weakObservable_hasDerivAt phi hphi hcompact t ht
  have hraw := yaglomDensity_weakObservable_hasDerivAt_raw phi hphi hcompact t ht
  have heq := hweak.unique hraw
  rw [heq]
  simp only [weakObservable, halfLineTestPairing]
  have hfirst : IntegrableOn
      (fun x : ℝ ↦ phi x * yaglomDensity t x) (Ici (0 : ℝ)) :=
    ((hphi.continuous.mul (continuous_yaglomDensity t))
      |>.integrable_of_hasCompactSupport hcompact.mul_right).integrableOn
  have hsecond : IntegrableOn
      (fun x : ℝ ↦ (x * phi x) * yaglomDensity t x) (Ici (0 : ℝ)) := by
    exact (((continuous_id.mul hphi.continuous).mul (continuous_yaglomDensity t))
      |>.integrable_of_hasCompactSupport hcompact.mul_left.mul_right).integrableOn
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hfirst.const_mul (-2 / t)) (hsecond.const_mul (2 / t ^ 2))]
  apply integral_congr_ae
  filter_upwards with x
  unfold yaglomDensity
  field_simp [ht.ne']
  ring

/-- Tested explicit observables are continuous on positive-time windows. -/
theorem continuousOn_yaglomDensity_weakObservable
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (eta T : ℝ) (heta : 0 < eta) :
    ContinuousOn (weakObservable (fun s ↦ yaglomDensity s) phi) (Icc eta T) := by
  intro t ht
  exact (yaglomDensity_weakObservable_hasDerivAt_raw phi hphi hcompact t
    (heta.trans_le ht.1)).continuousAt.continuousWithinAt

/-- The explicit weak generator is continuous on positive-time windows. -/
theorem continuousOn_yaglomDensity_weakEquationRhs
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hcompact : HasCompactSupport phi) (eta T : ℝ) (heta : 0 < eta) :
    ContinuousOn (weakEquationRhs (fun s ↦ yaglomDensity s) phi) (Icc eta T) := by
  let psi : ℝ → ℝ := fun x ↦ x * phi x
  have hpsi : ContDiff ℝ 1 psi := contDiff_id.mul hphi
  have hpsiCompact : HasCompactSupport psi := hcompact.mul_left
  have hcombo : ContinuousOn
      (fun t ↦ (-2 / t) * weakObservable (fun s ↦ yaglomDensity s) phi t +
        (2 / t ^ 2) * weakObservable (fun s ↦ yaglomDensity s) psi t)
      (Icc eta T) := by
    intro t ht
    have htpos : 0 < t := heta.trans_le ht.1
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.add
    · apply ContinuousAt.mul
      · exact continuousAt_const.div continuousAt_id htpos.ne'
      · exact (yaglomDensity_weakObservable_hasDerivAt_raw
          phi hphi hcompact t htpos).continuousAt
    · apply ContinuousAt.mul
      · exact continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 htpos.ne')
      · exact (yaglomDensity_weakObservable_hasDerivAt_raw
          psi hpsi hpsiCompact t htpos).continuousAt
  apply hcombo.congr
  intro t ht
  simpa only [psi] using
    (weakEquationRhs_yaglomDensity_eq_combo phi hphi hcompact t
      (heta.trans_le ht.1))

/-- U46 for the explicit Yaglom density, including its boundary trace. -/
theorem yaglomDensity_hasWeakEquationOn
    (eta T : ℝ) (heta : 0 < eta) :
    HasWeakEquationOn (fun s ↦ yaglomDensity s) (Icc eta T) := by
  intro phi htest
  exact hasTimeIntegratedWeakEquationOn_of_pointwise_derivative
    (fun s ↦ yaglomDensity s) phi eta T
    (continuousOn_yaglomDensity_weakObservable phi htest.1 htest.2 eta T heta)
    (continuousOn_yaglomDensity_weakEquationRhs phi htest.1 htest.2 eta T heta)
    (fun t ht ↦ yaglomDensity_weakObservable_hasDerivAt
      phi htest.1 htest.2 t (heta.trans ht.1))

/-- Tested observables agree for densities equal on the half-line. -/
theorem weakObservable_congr
    {u v : ℝ → ℝ → ℝ} {phi : ℝ → ℝ} {t : ℝ}
    (huv : Set.EqOn (u t) (v t) (Ici (0 : ℝ))) :
    weakObservable u phi t = weakObservable v phi t := by
  unfold weakObservable halfLineTestPairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [huv hx]
/-- Quadratic weak pairings agree for densities equal on the half-line. -/
theorem weakQuadraticPairing_congr
    {u v phi : ℝ → ℝ}
    (huv : Set.EqOn u v (Ici (0 : ℝ))) :
    weakQuadraticPairing phi u = weakQuadraticPairing phi v := by
  unfold weakQuadraticPairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  rw [huv hx, huv hy]

/-- Weak generators agree for densities equal on the half-line. -/
theorem weakEquationRhs_congr
    {u v : ℝ → ℝ → ℝ} {phi : ℝ → ℝ} {t : ℝ}
    (huv : Set.EqOn (u t) (v t) (Ici (0 : ℝ))) :
    weakEquationRhs u phi t = weakEquationRhs v phi t := by
  unfold weakEquationRhs
  rw [huv (by simp), weakQuadraticPairing_congr huv]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [huv hx]

/-- Transfer a weak equation across pointwise equality on a compact time window. -/
theorem hasWeakEquationOn_congr_Icc
    {u v : ℝ → ℝ → ℝ} {eta T : ℝ}
    (huv : ∀ t ∈ Icc eta T, Set.EqOn (u t) (v t) (Ici (0 : ℝ)))
    (hv : HasWeakEquationOn v (Icc eta T)) :
    HasWeakEquationOn u (Icc eta T) := by
  intro phi hphi a ha b hb hab
  have hsource := hv phi hphi a ha b hb hab
  rw [weakObservable_congr (huv b hb),
    weakObservable_congr (huv a ha)]
  rw [hsource]
  apply intervalIntegral.integral_congr
  intro s hs
  apply weakEquationRhs_congr
  apply Set.EqOn.symm
  apply huv s
  rw [uIcc_of_le hab] at hs
  exact ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩

end

end DerridaRetaux

