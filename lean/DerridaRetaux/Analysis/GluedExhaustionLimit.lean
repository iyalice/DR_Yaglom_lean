import DerridaRetaux.Analysis.GridCompactness

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Glue compatible compact-exhaustion limits on the whole positive-time,
nonnegative-space half-strip. Values outside that domain are set to zero. -/
def gluedExhaustionLimit
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t x : ℝ) : ℝ :=
  if h : 0 < t ∧ 0 ≤ x then
    let hex : ∃ k : ℕ, (t, x) ∈ gridExhaustionRectangle k :=
      exists_mem_gridExhaustionRectangle h.1 h.2
    g (Classical.choose hex) ⟨(t, x), Classical.choose_spec hex⟩
  else 0

/-- On any exhaustion rectangle the glued function agrees with that fixed
local representative. -/
theorem gluedExhaustionLimit_eq_local
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩)
    (k : ℕ) (t x : ℝ) (htx : (t, x) ∈ gridExhaustionRectangle k) :
    gluedExhaustionLimit g t x = g k ⟨(t, x), htx⟩ := by
  have ht : 0 < t := lt_of_lt_of_le (by positivity) htx.1.1
  have hx : 0 ≤ x := htx.2.1
  let hex : ∃ l : ℕ, (t, x) ∈ gridExhaustionRectangle l :=
    exists_mem_gridExhaustionRectangle ht hx
  let l : ℕ := Classical.choose hex
  let p : gridExhaustionRectangle l :=
    ⟨(t, x), Classical.choose_spec hex⟩
  rw [gluedExhaustionLimit, dif_pos ⟨ht, hx⟩]
  change g l p = g k ⟨(t, x), htx⟩
  let q : ℕ := max l k
  calc
    g l p = g q ⟨(p : ℝ × ℝ),
        gridExhaustionRectangle_mono (le_max_left l k) p.property⟩ :=
      hcompat (le_max_left l k) p
    _ = g q ⟨((⟨(t, x), htx⟩ : gridExhaustionRectangle k) : ℝ × ℝ),
        gridExhaustionRectangle_mono (le_max_right l k) htx⟩ := by
      congr 2
    _ = g k ⟨(t, x), htx⟩ :=
      (hcompat (le_max_right l k) ⟨(t, x), htx⟩).symm

/-- The glued two-variable limit is continuous on each compact exhaustion
rectangle. -/
theorem continuousOn_gluedExhaustionLimit_rectangle
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩)
    (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ gluedExhaustionLimit g p.1 p.2)
      (gridExhaustionRectangle k) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun p : gridExhaustionRectangle k ↦
    gluedExhaustionLimit g ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2))
  have heq :
      (fun p : gridExhaustionRectangle k ↦
        gluedExhaustionLimit g ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2)) = g k := by
    funext p
    exact gluedExhaustionLimit_eq_local g hcompat k
      ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2) p.property
  rw [heq]
  exact (g k).continuous

/-- The diagonal interpolants converge uniformly on every exhaustion rectangle
to the single glued limit. -/
theorem tendstoUniformlyOn_gluedExhaustionLimit
    (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p : gridExhaustionRectangle k ↦
        gluedExhaustionLimit g ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2))
      atTop := by
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible
      (fun N q ↦ gridBilinearInterp N (a N) q.1 q.2)
      phi g hlim hkl p
  intro k
  have heq : (fun p : gridExhaustionRectangle k ↦ g k p) =
      (fun p : gridExhaustionRectangle k ↦
        gluedExhaustionLimit g ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2)) := by
    funext p
    exact (gluedExhaustionLimit_eq_local g hcompat k
      ((p : ℝ × ℝ).1) ((p : ℝ × ℝ).2) p.property).symm
  rw [← heq]
  exact hlim k

end

end DerridaRetaux
