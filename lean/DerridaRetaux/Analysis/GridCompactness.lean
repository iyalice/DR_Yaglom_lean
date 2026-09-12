import DerridaRetaux.Analysis.GridEquicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-!
# Countable diagonal compactness for grid interpolants

This file isolates the compactness step used after the quantitative interpolation estimates.
It does not prove the discrete estimates from the source.  Instead, it turns compact coordinate
closures into one strictly increasing diagonal subsequence, and then supplies the compact-rectangle
specialization needed for bilinear grid interpolants.
-/

namespace DerridaRetaux

noncomputable section

open Filter Set Topology

/-- A countable product of compact coordinate sets contains a convergent subsequence of every
sequence that stays in the product.  The extracted map is strictly increasing, hence cofinal.

This is the reusable diagonal step: compactness is supplied independently in every coordinate,
while convergence of the product subsequence is exactly coordinatewise convergence. -/
theorem countable_diagonal_subsequence
    {Y : ℕ → Type*} [∀ k, TopologicalSpace (Y k)]
    [∀ k, FirstCountableTopology (Y k)]
    (Q : ∀ k, Set (Y k)) (hQ : ∀ k, IsCompact (Q k))
    (v : ℕ → ∀ k, Y k) (hv : ∀ n k, v n k ∈ Q k) :
    ∃ y : ∀ k, Y k, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto phi atTop atTop ∧
        ∀ k, Tendsto (fun n ↦ v (phi n) k) atTop (𝓝 (y k)) := by
  have hcompact : IsCompact (Set.pi Set.univ Q) := isCompact_univ_pi hQ
  have hv_product : ∀ n, v n ∈ Set.pi Set.univ Q := by
    intro n k _
    exact hv n k
  obtain ⟨y, _hy, phi, hphi, hlim⟩ := hcompact.tendsto_subseq hv_product
  refine ⟨y, phi, hphi, hphi.tendsto_atTop, ?_⟩
  intro k
  simpa [Function.comp_def] using (tendsto_pi_nhds.mp hlim k)

/-- Restrict a continuous function to a compact set and package it with the sup metric. -/
def compactRestriction {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f) :
    BoundedContinuousFunction K ℝ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K ↦ f x, hf.comp continuous_subtype_val⟩

@[simp]
theorem compactRestriction_apply {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f) (x : K) :
    compactRestriction hK f hf x = f x := by
  rfl

/-- A uniform bound after discarding a finite prefix. -/
def EventuallyUniformlyBoundedOn {X : Type*} (F : ℕ → X → ℝ) (K : Set X) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x ∈ K, |F n x| ≤ C

/-- On a compact set, continuity bounds the discarded finite prefix, so an eventual common bound
can be enlarged to a common bound for the full sequence. -/
theorem exists_uniform_bound_of_eventuallyUniformlyBoundedOn
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (F : ℕ → X → ℝ) (hcontinuous : ∀ n, Continuous (F n))
    (heventual : EventuallyUniformlyBoundedOn F K) :
    ∃ C : ℝ, ∀ n x, x ∈ K → |F n x| ≤ C := by
  obtain ⟨C, N₀, hC⟩ := heventual
  let B : ℝ := Finset.sum (Finset.range N₀) fun n ↦
    ‖compactRestriction hK (F n) (hcontinuous n)‖
  refine ⟨max C B, ?_⟩
  intro n x hx
  by_cases hn : N₀ ≤ n
  · exact (hC n hn x hx).trans (le_max_left C B)
  · have hn_mem : n ∈ Finset.range N₀ := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have heval :
        |F n x| ≤ ‖compactRestriction hK (F n) (hcontinuous n)‖ := by
      simpa only [compactRestriction_apply, Real.norm_eq_abs] using
        (compactRestriction hK (F n) (hcontinuous n)).norm_coe_le_norm ⟨x, hx⟩
    calc
      |F n x| ≤ ‖compactRestriction hK (F n) (hcontinuous n)‖ := heval
      _ ≤ B := by
        exact Finset.single_le_sum (fun m _ ↦ norm_nonneg
          (compactRestriction hK (F m) (hcontinuous m))) hn_mem
      _ ≤ max C B := le_max_right C B

/-- The compact coordinate supplied by Arzelà--Ascoli on one compact set.

The two substantive hypotheses are deliberately explicit: every member of the family is bounded
by the same `C` on `K`, and the family is equicontinuous on `K`.  No subsequential convergence is
assumed. -/
theorem isCompact_closure_range_compactRestriction
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (F : ℕ → X → ℝ) (hcontinuous : ∀ n, Continuous (F n))
    (C : ℝ) (hbound : ∀ n x, x ∈ K → |F n x| ≤ C)
    (hequicontinuous : EquicontinuousOn F K) :
    IsCompact
      (closure (Set.range fun n ↦ compactRestriction hK (F n) (hcontinuous n))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (BoundedContinuousFunction K ℝ) :=
    Set.range fun n ↦ compactRestriction hK (F n) (hcontinuous n)
  have hin_interval : ∀ (f : BoundedContinuousFunction K ℝ) (x : K),
      f ∈ A → f x ∈ Set.Icc (-C) C := by
    intro f x hf
    obtain ⟨n, rfl⟩ := hf
    exact abs_le.mp (hbound n x x.property)
  have hrestricted : Equicontinuous (K.restrict ∘ F) :=
    (equicontinuous_restrict_iff F).mpr hequicontinuous
  have hA : Equicontinuous ((↑) : A → K → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff_pair]
    intro epsilon hepsilon
    have hx := hrestricted x
    rw [Metric.equicontinuousAt_iff_pair] at hx
    obtain ⟨U, hU, hpair⟩ := hx epsilon hepsilon
    refine ⟨U, hU, ?_⟩
    intro y hy z hz f
    obtain ⟨n, hn⟩ := f.property
    rw [← hn]
    simpa [A, Function.comp_def] using hpair y hy z hz n
  exact BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-C) C) isCompact_Icc A hin_interval hA

/-- The rational/integer exhaustion rectangles
`[1/(k+1), k+1] × [0, k+1]` used for the local diagonal argument. -/
def gridExhaustionRectangle (k : ℕ) : Set (ℝ × ℝ) :=
  compactRectangle ((k + 1 : ℕ) : ℝ)⁻¹ ((k + 1 : ℕ) : ℝ) ((k + 1 : ℕ) : ℝ)

theorem isCompact_gridExhaustionRectangle (k : ℕ) :
    IsCompact (gridExhaustionRectangle k) := by
  exact isCompact_Icc.prod isCompact_Icc

theorem gridExhaustionRectangle_mono {k l : ℕ} (hkl : k ≤ l) :
    gridExhaustionRectangle k ⊆ gridExhaustionRectangle l := by
  have hsucc_nat : k + 1 ≤ l + 1 := Nat.add_le_add_right hkl 1
  have hsucc : (((k + 1 : ℕ) : ℝ)) ≤ (((l + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hsucc_nat
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hlpos : 0 < (((l + 1 : ℕ) : ℝ)) := by positivity
  have hinv : (((l + 1 : ℕ) : ℝ))⁻¹ ≤ (((k + 1 : ℕ) : ℝ))⁻¹ :=
    (inv_le_inv₀ hlpos hkpos).mpr hsucc
  rintro p ⟨⟨ht_lower, ht_upper⟩, hx_lower, hx_upper⟩
  exact ⟨⟨hinv.trans ht_lower, ht_upper.trans hsucc⟩,
    hx_lower, hx_upper.trans hsucc⟩

/-- The exhaustion covers the positive-time, nonnegative-space half-strip. -/
theorem exists_mem_gridExhaustionRectangle {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    ∃ k : ℕ, (t, x) ∈ gridExhaustionRectangle k := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt ht
  obtain ⟨kt, hkt⟩ := exists_nat_ge t
  obtain ⟨kx, hkx⟩ := exists_nat_ge x
  let k : ℕ := max k₀ (max kt kx)
  have hk₀k : k₀ ≤ k := le_max_left _ _
  have hktk : kt ≤ k := (le_max_left kt kx).trans (le_max_right k₀ (max kt kx))
  have hkxk : kx ≤ k := (le_max_right kt kx).trans (le_max_right k₀ (max kt kx))
  have hdenom : (((k₀ + 1 : ℕ) : ℝ)) ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hk₀k 1
  have hk₀pos : 0 < (((k₀ + 1 : ℕ) : ℝ)) := by positivity
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hlower : (((k + 1 : ℕ) : ℝ))⁻¹ ≤ t := by
    calc
      (((k + 1 : ℕ) : ℝ))⁻¹ ≤ (((k₀ + 1 : ℕ) : ℝ))⁻¹ :=
        (inv_le_inv₀ hkpos hk₀pos).mpr hdenom
      _ ≤ t := by
        simpa [Nat.cast_add, Nat.cast_one, one_div] using hk₀.le
  have htupper : t ≤ (((k + 1 : ℕ) : ℝ)) := by
    have hkt_succ : kt ≤ k + 1 := hktk.trans (Nat.le_succ k)
    exact hkt.trans (by exact_mod_cast hkt_succ)
  have hxupper : x ≤ (((k + 1 : ℕ) : ℝ)) := by
    have hkx_succ : kx ≤ k + 1 := hkxk.trans (Nat.le_succ k)
    exact hkx.trans (by exact_mod_cast hkx_succ)
  exact ⟨k, ⟨⟨hlower, htupper⟩, hx, hxupper⟩⟩

/-- Limits obtained on two nested exhaustion rectangles agree on their common points.  Thus the
coordinate limits furnished by the product argument form a coherent local limit family. -/
theorem exhaustionLimits_compatible
    (F : ℕ → (ℝ × ℝ) → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦ F (phi n) p)
      (fun p ↦ g k p) atTop)
    {k l : ℕ} (hkl : k ≤ l) (p : gridExhaustionRectangle k) :
    g k p = g l ⟨(p : ℝ × ℝ), gridExhaustionRectangle_mono hkl p.property⟩ := by
  let q : gridExhaustionRectangle l :=
    ⟨(p : ℝ × ℝ), gridExhaustionRectangle_mono hkl p.property⟩
  have hk_limit := (hlim k).tendsto_at p
  have hl_limit := (hlim l).tendsto_at q
  apply tendsto_nhds_unique hk_limit
  simpa [q] using hl_limit

/-- Arzelà--Ascoli on all rational/integer exhaustion rectangles, followed by the countable
product diagonal theorem.  The result is one strictly increasing, cofinal subsequence that
converges uniformly on every exhaustion rectangle.

Both analytic inputs are hypotheses: a common bound and equicontinuity on each rectangle. -/
theorem exists_diagonal_subsequence_tendstoUniformlyOn_exhaustion
    (F : ℕ → (ℝ × ℝ) → ℝ) (hcontinuous : ∀ n, Continuous (F n))
    (hbound : ∀ k, ∃ C : ℝ, ∀ n p, p ∈ gridExhaustionRectangle k → |F n p| ≤ C)
    (hequicontinuous : ∀ k, EquicontinuousOn F (gridExhaustionRectangle k)) :
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          ∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦ F (phi n) p)
            (fun p ↦ g k p) atTop := by
  choose C hC using hbound
  let Q : ∀ k, Set (BoundedContinuousFunction (gridExhaustionRectangle k) ℝ) :=
    fun k ↦ closure (Set.range fun n ↦
      compactRestriction (isCompact_gridExhaustionRectangle k) (F n) (hcontinuous n))
  let v : ℕ → ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ :=
    fun n k ↦ compactRestriction (isCompact_gridExhaustionRectangle k) (F n) (hcontinuous n)
  have hQ : ∀ k, IsCompact (Q k) := by
    intro k
    exact isCompact_closure_range_compactRestriction
      (isCompact_gridExhaustionRectangle k) F hcontinuous (C k) (hC k)
        (hequicontinuous k)
  have hv : ∀ n k, v n k ∈ Q k := by
    intro n k
    exact subset_closure (Set.mem_range_self n)
  obtain ⟨g, phi, hphi, hphi_cofinal, hlim⟩ :=
    countable_diagonal_subsequence Q hQ v hv
  refine ⟨g, phi, hphi, hphi_cofinal, ?_⟩
  intro k
  have hu : TendstoUniformly
      (fun n ↦ (v (phi n) k : gridExhaustionRectangle k → ℝ))
      (g k : gridExhaustionRectangle k → ℝ) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hlim k)
  simpa [v] using hu

/-- Eventual bounds and eventual `L¹` equicontinuity are sufficient for the preceding compactness
theorem: compactness controls each discarded finite prefix. -/
theorem exists_diagonal_subsequence_of_eventuallyOn_exhaustion
    (F : ℕ → (ℝ × ℝ) → ℝ) (hcontinuous : ∀ n, Continuous (F n))
    (hbound : ∀ k, EventuallyUniformlyBoundedOn F (gridExhaustionRectangle k))
    (hequicontinuous : ∀ k,
      EventuallyEquicontinuousOnL1 F (gridExhaustionRectangle k)) :
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          ∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦ F (phi n) p)
            (fun p ↦ g k p) atTop := by
  apply exists_diagonal_subsequence_tendstoUniformlyOn_exhaustion F hcontinuous
  · intro k
    exact exists_uniform_bound_of_eventuallyUniformlyBoundedOn
      (isCompact_gridExhaustionRectangle k) F hcontinuous (hbound k)
  · intro k
    exact (hequicontinuous k).equicontinuousOn hcontinuous

/-- Source-facing compactness wrapper for the literal scaled bilinear interpolants.  Its premises
are exactly eventual boundedness and the eventual modulus on every exhaustion rectangle; it does
not assume the resulting subsequential convergence. -/
theorem exists_gridBilinearInterp_diagonal_subsequence
    (a : ℕ → ℕ → ℕ → ℝ)
    (hbound : ∀ k, EventuallyUniformlyBoundedOn
      (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2) (gridExhaustionRectangle k))
    (hequicontinuous : ∀ k, EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2) (gridExhaustionRectangle k)) :
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          ∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦
              gridBilinearInterp (phi n) (a (phi n))
                (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
            (fun p ↦ g k p) atTop := by
  exact exists_diagonal_subsequence_of_eventuallyOn_exhaustion
    (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2)
    (fun N ↦ continuous_gridBilinearInterp N (a N)) hbound hequicontinuous

/-- Uniform convergence of the interpolants at `t = 1`, together with a vanishing one-step
spatial error, transfers convergence to the floor-grid readout.  This is the precise bridge used
after diagonal compactness; the spatial error estimate remains an explicit premise. -/
theorem gridNodeReadout_tendsto_of_uniformOn_exhaustion
    (k : ℕ) (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (stepError : ℕ → ℝ) (x : ℝ)
    (hx : (1, x) ∈ gridExhaustionRectangle k)
    (hphi_cofinal : Tendsto phi atTop atTop)
    (huniform : TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g p) atTop)
    (hspace : ∀ N : ℕ, 0 < N → ∀ j : ℕ,
      |a N N (j + 1) - a N N j| ≤ stepError N)
    (hstep_zero : Tendsto (fun n ↦ stepError (phi n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ a (phi n) (phi n) (gridIndex (phi n) x)) atTop
      (𝓝 (g ⟨(1, x), hx⟩)) := by
  let p : gridExhaustionRectangle k := ⟨(1, x), hx⟩
  have hinterp : Tendsto
      (fun n ↦ gridBilinearInterp (phi n) (a (phi n)) 1 x) atTop
      (𝓝 (g p)) := by
    simpa [p] using huniform.tendsto_at p
  have hphi_positive : ∀ᶠ n in atTop, 0 < phi n :=
    hphi_cofinal (eventually_gt_atTop 0)
  have herror_bound : ∀ᶠ n in atTop,
      dist (gridBilinearInterp (phi n) (a (phi n)) 1 x)
        (a (phi n) (phi n) (gridIndex (phi n) x)) ≤ stepError (phi n) := by
    filter_upwards [hphi_positive] with n hn
    simpa only [Real.dist_eq] using
      abs_gridBilinearInterp_time_one_sub_floor_le_of_bound
        (phi n) (a (phi n)) x (stepError (phi n)) hn (hspace (phi n) hn)
  have herror : Tendsto
      (fun n ↦ dist (gridBilinearInterp (phi n) (a (phi n)) 1 x)
        (a (phi n) (phi n) (gridIndex (phi n) x))) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) herror_bound hstep_zero
  exact hinterp.congr_dist herror

end

end DerridaRetaux
