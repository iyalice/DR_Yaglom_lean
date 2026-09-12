import DerridaRetaux.Analysis.GluedExhaustionLimit
import DerridaRetaux.Analysis.UniformLatticeCriterion
import DerridaRetaux.Analysis.TimeRiemannLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Uniform convergence on the two-dimensional exhaustion supplies the
local-uniform lattice density at every fixed positive macroscopic time.  The
generation is the literal natural-floor grid index, so this result is the
moving-time analogue of the older time-one readout theorem. -/
theorem locallyUniformLatticeDensity_of_gluedExhaustion_at_time
    (rho : ℕ → Seq) (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t : ℝ) (ht : 0 < t)
    (hphi : Tendsto phi atTop atTop)
    (hnode : ∀ n j : ℕ,
      a (phi n) (gridIndex (phi n) t) j =
        (phi n : ℝ) ^ 2 * rho n j)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformLatticeDensity rho phi
      (fun x ↦ gluedExhaustionLimit g t x) := by
  apply locallyUniformLatticeDensity_of_eventually_epsilon
  intro R ε hε
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (a N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle ht
    (show 0 ≤ (R : ℝ) + 1 by positivity)
  let K : ℕ := k + 1
  have htLower : (((K + 1 : ℕ) : ℝ))⁻¹ < t := by
    have hstep : (((k + 2 : ℕ) : ℝ))⁻¹ <
        (((k + 1 : ℕ) : ℝ))⁻¹ := by
      simpa only [one_div] using
        (one_div_lt_one_div_of_lt
          (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)
          (show ((k + 1 : ℕ) : ℝ) < ((k + 2 : ℕ) : ℝ) by norm_num))
    exact hstep.trans_le hk.1.1
  have htUpper : t < ((K + 1 : ℕ) : ℝ) := by
    exact hk.1.2.trans_lt (by dsimp only [K]; norm_num)
  have hRUpper : (R : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    have hR : (R : ℝ) ≤ (R : ℝ) + 1 := by linarith
    exact hR.trans (hk.2.2.trans (by dsimp only [K]; norm_num))
  let tn : ℕ → ℝ := fun n ↦
    (gridIndex (phi n) t : ℝ) / (phi n : ℝ)
  have htn : Tendsto tn atTop (nhds t) := by
    exact (gridIndex_div_tendsto t ht.le).comp hphi
  have htnRect : ∀ᶠ n : ℕ in atTop,
      (((K + 1 : ℕ) : ℝ))⁻¹ ≤ tn n ∧
        tn n ≤ ((K + 1 : ℕ) : ℝ) := by
    have hnear : ∀ᶠ n : ℕ in atTop,
        tn n ∈ Ioo (((K + 1 : ℕ) : ℝ))⁻¹
          ((K + 1 : ℕ) : ℝ) :=
      htn (Ioo_mem_nhds htLower htUpper)
    exact hnear.mono fun _ hn ↦ ⟨hn.1.le, hn.2.le⟩
  have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n :=
    hphi (eventually_gt_atTop 0)
  letI : CompactSpace (gridExhaustionRectangle K) :=
    isCompact_iff_compactSpace.mp (isCompact_gridExhaustionRectangle K)
  have hinterp := (Metric.tendstoUniformly_iff.mp (hlim K))
    (ε / 2) (half_pos hε)
  have hguniform : UniformContinuous (g K) :=
    CompactSpace.uniformContinuous_of_continuous (g K).continuous
  obtain ⟨δ, hδ, hgmod⟩ :=
    Metric.uniformContinuous_iff.mp hguniform (ε / 2) (half_pos hε)
  have htnClose : ∀ᶠ n : ℕ in atTop, dist (tn n) t < δ :=
    (Metric.tendsto_nhds.mp htn) δ hδ
  filter_upwards [hphiPos, htnRect, hinterp, htnClose] with n hn htnK hninterp hnclose
  intro _hn j hj
  let x : ℝ := (j : ℝ) / (phi n : ℝ)
  have hphiReal : (0 : ℝ) < (phi n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg j) hphiReal.le
  have hxR : x ≤ (R : ℝ) := by
    dsimp only [x]
    rw [div_le_iff₀ hphiReal]
    exact_mod_cast hj
  have hpNow : (tn n, x) ∈ gridExhaustionRectangle K :=
    ⟨htnK, hx0, hxR.trans hRUpper⟩
  have hpLimit : (t, x) ∈ gridExhaustionRectangle K :=
    ⟨⟨htLower.le, htUpper.le⟩, hx0, hxR.trans hRUpper⟩
  let pNow : gridExhaustionRectangle K := ⟨(tn n, x), hpNow⟩
  let pLimit : gridExhaustionRectangle K := ⟨(t, x), hpLimit⟩
  have hpdist : dist pNow pLimit < δ := by
    change dist (tn n, x) (t, x) < δ
    simpa only [Prod.dist_eq, dist_self, max_eq_left, dist_nonneg] using hnclose
  have hgclose : dist (g K pNow) (g K pLimit) < ε / 2 :=
    hgmod hpdist
  have hgrid :
      gridBilinearInterp (phi n) (a (phi n)) (tn n) x =
        (phi n : ℝ) ^ 2 * rho n j := by
    rw [show tn n = (gridIndex (phi n) t : ℝ) / (phi n : ℝ) by rfl,
      show x = (j : ℝ) / (phi n : ℝ) by rfl,
      gridBilinearInterp_at_node (phi n) (gridIndex (phi n) t) j
        (a (phi n)) hn,
      hnode]
  have hglue : gluedExhaustionLimit g t x = g K pLimit :=
    gluedExhaustionLimit_eq_local g hcompat K t x hpLimit
  rw [← hgrid, hglue, ← Real.dist_eq]
  exact (dist_triangle _ (g K pNow) _).trans_lt (by
    have hfirst : dist
        (gridBilinearInterp (phi n) (a (phi n)) (tn n) x)
        (g K pNow) < ε / 2 := by
      simpa only [pNow, dist_comm] using hninterp pNow
    linarith)

end

end DerridaRetaux
