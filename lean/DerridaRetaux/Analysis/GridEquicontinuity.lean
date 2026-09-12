import DerridaRetaux.Analysis.GridInterpolation
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false

/-!
# Quantitative bounds for scaled bilinear interpolation

This file is the analytic bridge from *explicitly assumed* discrete node bounds and moduli to
bounds and moduli for the literal interpolants defined in `GridInterpolation`.  It deliberately
does not assert the source estimates `eq:sup`, `eq:spmod`, or `eq:timemod`: those estimates remain
upstream obligations and must be supplied through the hypotheses below.
-/

namespace DerridaRetaux

noncomputable section

/-- The compact rectangle used in the local compactness argument. -/
def compactRectangle (eta T R : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc eta T ×ˢ Set.Icc 0 R

/-- Tail epsilon--delta equicontinuity, measured with the coordinatewise `L¹` distance.

This is the exact form needed for asymptotic compactness: a finite prefix of the sequence is
irrelevant, while all sufficiently fine interpolants share one delta for each epsilon. -/
def EventuallyEquicontinuousOnL1 (F : ℕ → (ℝ × ℝ) → ℝ) (K : Set (ℝ × ℝ)) : Prop :=
  ∀ epsilon > 0, ∃ delta > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p ∈ K, ∀ q ∈ K,
    |p.1 - q.1| + |p.2 - q.2| < delta → |F N p - F N q| < epsilon

/-- Tail epsilon--delta control plus continuity of every individual function gives ordinary
equicontinuity of the entire sequence.  The finitely many indices before the tail cutoff are
handled by their individual continuity. -/
theorem EventuallyEquicontinuousOnL1.equicontinuousOn
    {F : ℕ → (ℝ × ℝ) → ℝ} {K : Set (ℝ × ℝ)}
    (htail : EventuallyEquicontinuousOnL1 F K)
    (hcontinuous : ∀ N : ℕ, Continuous (F N)) : EquicontinuousOn F K := by
  intro p hp U hU
  obtain ⟨epsilon, hepsilon, hepsilonU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨delta, hdelta, N₀, hN₀⟩ := htail epsilon hepsilon
  have hnear :
      ∀ᶠ q in nhdsWithin p K, |p.1 - q.1| + |p.2 - q.2| < delta := by
    have hopen : IsOpen {q : ℝ × ℝ | |p.1 - q.1| + |p.2 - q.2| < delta} := by
      have hcontinuous_distance :
          Continuous (fun q : ℝ × ℝ ↦ |p.1 - q.1| + |p.2 - q.2|) := by
        fun_prop
      exact isOpen_lt hcontinuous_distance continuous_const
    have hp_mem : p ∈ {q : ℝ × ℝ | |p.1 - q.1| + |p.2 - q.2| < delta} := by
      simpa using hdelta
    have hnear_full : ∀ᶠ q in nhds p, |p.1 - q.1| + |p.2 - q.2| < delta :=
      hopen.mem_nhds hp_mem
    exact hnear_full.filter_mono inf_le_left
  have hfinite :
      ∀ᶠ q in nhdsWithin p K, ∀ N ∈ Finset.range N₀, dist (F N p) (F N q) < epsilon := by
    rw [Finset.eventually_all]
    intro N _
    have hN_cont : ∀ᶠ q in nhds p, dist (F N q) (F N p) < epsilon :=
      Metric.continuousAt_iff'.mp (hcontinuous N).continuousAt epsilon hepsilon
    exact (hN_cont.filter_mono inf_le_left).mono (fun q hq ↦ by simpa [dist_comm] using hq)
  have htail_event :
      ∀ᶠ q in nhdsWithin p K, ∀ N ≥ N₀, dist (F N p) (F N q) < epsilon := by
    filter_upwards [hnear, self_mem_nhdsWithin] with q hq_near hq
    intro N hNN₀
    simpa [Real.dist_eq] using hN₀ N hNN₀ p hp q hq hq_near
  filter_upwards [hfinite, htail_event] with q hq_finite hq_tail
  intro N
  apply hepsilonU
  by_cases hN : N < N₀
  · exact hq_finite N (Finset.mem_range.mpr hN)
  · exact hq_tail N (Nat.le_of_not_gt hN)

/-- The tail criterion specializes to ordinary equicontinuity for scaled bilinear interpolants,
because each interpolant is globally continuous. -/
theorem gridBilinearInterp_family_equicontinuousOn_of_eventually
    (a : ℕ → ℕ → ℕ → ℝ) (K : Set (ℝ × ℝ))
    (htail : EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2) K) :
    EquicontinuousOn (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2) K :=
  htail.equicontinuousOn (fun N ↦ continuous_gridBilinearInterp N (a N))

/-- Bilinear interpolation differs from its lower-left cell value by at most one spatial and one
temporal adjacent-node modulus. -/
theorem abs_bilinearInterp_sub_lowerLeft_le
    (a : ℕ → ℕ → ℝ) (t x spaceStep timeStep : ℝ)
    (hspace : ∀ n j : ℕ, |a n (j + 1) - a n j| ≤ spaceStep)
    (htime : ∀ n j : ℕ, |a (n + 1) j - a n j| ≤ timeStep) :
    |bilinearInterp a t x - a (gridIndex 1 t) (gridIndex 1 x)| ≤ timeStep + spaceStep := by
  let n := gridIndex 1 t
  let j := gridIndex 1 x
  let w₀₀ := bilinearWeight00 t x
  let w₀₁ := bilinearWeight01 t x
  let w₁₀ := bilinearWeight10 t x
  let w₁₁ := bilinearWeight11 t x
  have hw := bilinearWeights_nonneg t x
  have hw_sum := bilinearWeights_sum t x
  have hspace_nonneg : 0 ≤ spaceStep := (abs_nonneg _).trans (hspace n j)
  have htime_nonneg : 0 ≤ timeStep := (abs_nonneg _).trans (htime n j)
  have hdiag : |a (n + 1) (j + 1) - a n j| ≤ spaceStep + timeStep := by
    calc
      |a (n + 1) (j + 1) - a n j| =
          |(a (n + 1) (j + 1) - a (n + 1) j) + (a (n + 1) j - a n j)| := by
            congr 1
            ring
      _ ≤ |a (n + 1) (j + 1) - a (n + 1) j| + |a (n + 1) j - a n j| :=
        abs_add_le _ _
      _ ≤ spaceStep + timeStep := add_le_add (hspace (n + 1) j) (htime n j)
  have hidentity :
      bilinearInterp a t x - a n j =
        w₀₁ * (a n (j + 1) - a n j) +
          w₁₀ * (a (n + 1) j - a n j) +
          w₁₁ * (a (n + 1) (j + 1) - a n j) := by
    simp only [n, j, w₀₀, w₀₁, w₁₀, w₁₁]
    rw [bilinearInterp_eq_four_weights]
    simp only [bilinearWeight00, bilinearWeight01, bilinearWeight10, bilinearWeight11]
    ring
  have hw₀₁ : 0 ≤ w₀₁ := hw.2.1
  have hw₁₀ : 0 ≤ w₁₀ := hw.2.2.1
  have hw₁₁ : 0 ≤ w₁₁ := hw.2.2.2
  have hspace_coeff : w₀₁ + w₁₁ ≤ 1 := by
    dsimp only [w₀₀, w₀₁, w₁₀, w₁₁] at hw_sum ⊢
    linarith [hw.1, hw.2.2.1]
  have htime_coeff : w₁₀ + w₁₁ ≤ 1 := by
    dsimp only [w₀₀, w₀₁, w₁₀, w₁₁] at hw_sum ⊢
    linarith [hw.1, hw.2.1]
  rw [show gridIndex 1 t = n from rfl, show gridIndex 1 x = j from rfl, hidentity]
  calc
    |w₀₁ * (a n (j + 1) - a n j) +
          w₁₀ * (a (n + 1) j - a n j) +
          w₁₁ * (a (n + 1) (j + 1) - a n j)| ≤
        |w₀₁ * (a n (j + 1) - a n j)| +
          |w₁₀ * (a (n + 1) j - a n j)| +
          |w₁₁ * (a (n + 1) (j + 1) - a n j)| := by
            exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ = w₀₁ * |a n (j + 1) - a n j| +
          w₁₀ * |a (n + 1) j - a n j| +
          w₁₁ * |a (n + 1) (j + 1) - a n j| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw₀₁,
              abs_of_nonneg hw₁₀, abs_of_nonneg hw₁₁]
    _ ≤ w₀₁ * spaceStep + w₁₀ * timeStep +
          w₁₁ * (spaceStep + timeStep) := by
            gcongr
            · exact hspace n j
            · exact htime n j
    _ = (w₀₁ + w₁₁) * spaceStep +
          (w₁₀ + w₁₁) * timeStep := by ring
    _ ≤ 1 * spaceStep + 1 * timeStep :=
      add_le_add (mul_le_mul_of_nonneg_right hspace_coeff hspace_nonneg)
        (mul_le_mul_of_nonneg_right htime_coeff htime_nonneg)
    _ = timeStep + spaceStep := by ring

/-- Scaled version of `abs_bilinearInterp_sub_lowerLeft_le`. -/
theorem abs_gridBilinearInterp_sub_lowerLeft_le
    (N : ℕ) (a : ℕ → ℕ → ℝ) (t x spaceStep timeStep : ℝ) (hN : 0 < N)
    (hspace : ∀ n j : ℕ, |a n (j + 1) - a n j| ≤ spaceStep)
    (htime : ∀ n j : ℕ, |a (n + 1) j - a n j| ≤ timeStep) :
    |gridBilinearInterp N a t x - a (gridIndex N t) (gridIndex N x)| ≤
      timeStep + spaceStep := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  simpa using abs_bilinearInterp_sub_lowerLeft_le a ((N : ℝ) * t) ((N : ℝ) * x)
    spaceStep timeStep hspace htime

/-- A global node bound passes through the convex bilinear interpolant. -/
theorem abs_gridBilinearInterp_le_of_node_bound
    (N : ℕ) (a : ℕ → ℕ → ℝ) (C t x : ℝ) (hN : 0 < N)
    (hbound : ∀ n j : ℕ, |a n j| ≤ C) :
    |gridBilinearInterp N a t x| ≤ C := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  calc
    |bilinearInterp a ((N : ℝ) * t) ((N : ℝ) * x)| ≤
        cellAbsMax a (gridIndex 1 ((N : ℝ) * t))
          (gridIndex 1 ((N : ℝ) * x)) :=
      abs_bilinearInterp_le_cellAbsMax a ((N : ℝ) * t) ((N : ℝ) * x)
    _ ≤ C := by
      simp only [cellAbsMax]
      exact max_le (max_le (hbound _ _) (hbound _ _))
        (max_le (hbound _ _) (hbound _ _))

/-- A lower-left physical mesh point is close to the original coordinate. -/
theorem abs_gridPoint_sub_gridPoint_le
    (N : ℕ) (t s : ℝ) (hN : 0 < N) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |(gridIndex N t : ℝ) / (N : ℝ) - (gridIndex N s : ℝ) / (N : ℝ)| ≤
      |t - s| + 2 / (N : ℝ) := by
  have ht_offset := (abs_gridOffset_lt_inv N t hN ht).le
  have hs_offset := (abs_gridOffset_lt_inv N s hN hs).le
  calc
    |(gridIndex N t : ℝ) / (N : ℝ) - (gridIndex N s : ℝ) / (N : ℝ)| =
        |((gridIndex N t : ℝ) / (N : ℝ) - t) + (t - s) +
          (s - (gridIndex N s : ℝ) / (N : ℝ))| := by
            congr 1
            ring
    _ ≤ |(gridIndex N t : ℝ) / (N : ℝ) - t| + |t - s| +
          |s - (gridIndex N s : ℝ) / (N : ℝ)| := by
            exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ 1 / (N : ℝ) + |t - s| + 1 / (N : ℝ) := by
      gcongr
      simpa [abs_sub_comm] using ht_offset
    _ = |t - s| + 2 / (N : ℝ) := by ring

/-- Quantitative two-point modulus for a scaled bilinear interpolant.

The term `4 / N` is only the cost of replacing both points by their lower-left nodes.  The two
adjacent-step terms are the interpolation errors inside the endpoint cells. -/
theorem abs_gridBilinearInterp_sub_le_of_node_modulus
    (N : ℕ) (a : ℕ → ℕ → ℝ) (omega : ℝ → ℝ)
    (t x s y spaceStep timeStep : ℝ) (hN : 0 < N)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hs : 0 ≤ s) (hy : 0 ≤ y)
    (homega : Monotone omega)
    (hspace : ∀ n j : ℕ, |a n (j + 1) - a n j| ≤ spaceStep)
    (htime : ∀ n j : ℕ, |a (n + 1) j - a n j| ≤ timeStep)
    (hnode : ∀ n j n' j' : ℕ,
      |a n j - a n' j'| ≤
        omega (|(n : ℝ) / (N : ℝ) - (n' : ℝ) / (N : ℝ)| +
          |(j : ℝ) / (N : ℝ) - (j' : ℝ) / (N : ℝ)|)) :
    |gridBilinearInterp N a t x - gridBilinearInterp N a s y| ≤
      2 * (timeStep + spaceStep) +
        omega (|t - s| + |x - y| + 4 / (N : ℝ)) := by
  let nt := gridIndex N t
  let jt := gridIndex N x
  let ns := gridIndex N s
  let js := gridIndex N y
  have hp := abs_gridBilinearInterp_sub_lowerLeft_le N a t x spaceStep timeStep hN
    hspace htime
  have hq := abs_gridBilinearInterp_sub_lowerLeft_le N a s y spaceStep timeStep hN
    hspace htime
  have htime_nodes := abs_gridPoint_sub_gridPoint_le N t s hN ht hs
  have hspace_nodes := abs_gridPoint_sub_gridPoint_le N x y hN hx hy
  have hnode_dist :
      |(nt : ℝ) / (N : ℝ) - (ns : ℝ) / (N : ℝ)| +
          |(jt : ℝ) / (N : ℝ) - (js : ℝ) / (N : ℝ)| ≤
        |t - s| + |x - y| + 4 / (N : ℝ) := by
    dsimp only [nt, jt, ns, js]
    calc
      |(gridIndex N t : ℝ) / (N : ℝ) - (gridIndex N s : ℝ) / (N : ℝ)| +
          |(gridIndex N x : ℝ) / (N : ℝ) - (gridIndex N y : ℝ) / (N : ℝ)| ≤
          (|t - s| + 2 / (N : ℝ)) + (|x - y| + 2 / (N : ℝ)) :=
        add_le_add htime_nodes hspace_nodes
      _ = |t - s| + |x - y| + 4 / (N : ℝ) := by ring
  have hnodes :
      |a nt jt - a ns js| ≤ omega (|t - s| + |x - y| + 4 / (N : ℝ)) :=
    (hnode nt jt ns js).trans (homega hnode_dist)
  calc
    |gridBilinearInterp N a t x - gridBilinearInterp N a s y| =
        |(gridBilinearInterp N a t x - a nt jt) + (a nt jt - a ns js) +
          (a ns js - gridBilinearInterp N a s y)| := by
            congr 1
            ring
    _ ≤ |gridBilinearInterp N a t x - a nt jt| + |a nt jt - a ns js| +
          |a ns js - gridBilinearInterp N a s y| := by
            exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (timeStep + spaceStep) +
          omega (|t - s| + |x - y| + 4 / (N : ℝ)) +
          (timeStep + spaceStep) := by
      have hp' :
          |gridBilinearInterp N a t x - a nt jt| ≤ timeStep + spaceStep := by
        simpa [nt, jt] using hp
      have hq' :
          |a ns js - gridBilinearInterp N a s y| ≤ timeStep + spaceStep := by
        simpa [abs_sub_comm, ns, js] using hq
      exact add_le_add (add_le_add hp' hnodes) hq'
    _ = 2 * (timeStep + spaceStep) +
          omega (|t - s| + |x - y| + 4 / (N : ℝ)) := by ring

/-- Uniform node bounds imply uniform boundedness of the whole family on every compact rectangle.
The rectangle parameters appear in the conclusion; no bound outside its interpolants is claimed. -/
theorem gridBilinearInterp_family_uniformlyBoundedOn_rectangle
    (a : ℕ → ℕ → ℕ → ℝ) (eta T R C : ℝ)
    (hbound : ∀ N n j : ℕ, 0 < N → |a N n j| ≤ C) :
    ∀ N : ℕ, 0 < N → ∀ p ∈ compactRectangle eta T R,
      |gridBilinearInterp N (a N) p.1 p.2| ≤ C := by
  intro N hN p _
  exact abs_gridBilinearInterp_le_of_node_bound N (a N) C p.1 p.2 hN
    (fun n j ↦ hbound N n j hN)

/-- Discrete node moduli plus a vanishing numerical modulus imply tail equicontinuity of the
scaled bilinear family on each nonnegative compact rectangle.

The hypothesis `hsmall` contains only scalar rates.  In the source application it is the place
where the still-unproved estimates `eq:spmod` and `eq:timemod`, including their logarithmic rate,
must be inserted. -/
theorem gridBilinearInterp_family_eventuallyEquicontinuousOn_rectangle
    (a : ℕ → ℕ → ℕ → ℝ) (omega : ℝ → ℝ)
    (spaceStep timeStep : ℕ → ℝ) (eta T R : ℝ) (heta : 0 ≤ eta)
    (homega : Monotone omega)
    (hspace : ∀ N n j : ℕ, 0 < N →
      |a N n (j + 1) - a N n j| ≤ spaceStep N)
    (htime : ∀ N n j : ℕ, 0 < N →
      |a N (n + 1) j - a N n j| ≤ timeStep N)
    (hnode : ∀ N n j n' j' : ℕ, 0 < N →
      |a N n j - a N n' j'| ≤
        omega (|(n : ℝ) / (N : ℝ) - (n' : ℝ) / (N : ℝ)| +
          |(j : ℝ) / (N : ℝ) - (j' : ℝ) / (N : ℝ)|))
    (hsmall : ∀ epsilon > 0, ∃ delta > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < N ∧
        2 * (timeStep N + spaceStep N) + omega (delta + 4 / (N : ℝ)) < epsilon) :
    EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (a N) p.1 p.2) (compactRectangle eta T R) := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, N₀, hN₀⟩ := hsmall epsilon hepsilon
  refine ⟨delta, hdelta, N₀, ?_⟩
  intro N hNN₀ p hp q hq hpq
  have hN : 0 < N := (hN₀ N hNN₀).1
  have hpt : 0 ≤ p.1 := heta.trans hp.1.1
  have hpx : 0 ≤ p.2 := hp.2.1
  have hqt : 0 ≤ q.1 := heta.trans hq.1.1
  have hqx : 0 ≤ q.2 := hq.2.1
  calc
    |gridBilinearInterp N (a N) p.1 p.2 - gridBilinearInterp N (a N) q.1 q.2| ≤
        2 * (timeStep N + spaceStep N) +
          omega (|p.1 - q.1| + |p.2 - q.2| + 4 / (N : ℝ)) :=
      abs_gridBilinearInterp_sub_le_of_node_modulus N (a N) omega p.1 p.2 q.1 q.2
        (spaceStep N) (timeStep N) hN hpt hpx hqt hqx homega
        (fun n j ↦ hspace N n j hN) (fun n j ↦ htime N n j hN)
        (fun n j n' j' ↦ hnode N n j n' j' hN)
    _ ≤ 2 * (timeStep N + spaceStep N) + omega (delta + 4 / (N : ℝ)) := by
      apply add_le_add_left
      exact homega (add_le_add_right hpq.le _)
    _ < epsilon := (hN₀ N hNN₀).2

end

end DerridaRetaux
