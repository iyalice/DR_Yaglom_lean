import DerridaRetaux.Analysis.FloorTransportGeometry

set_option autoImplicit false

open Set

namespace DerridaRetaux

/-- Box-membership packaging of `floorTransportGeometry`. -/
theorem floorTransportBoxGeometry
    (N s : ℕ) (t₀ t x δ : ℝ) (R : ℕ)
    (hN : 0 < N) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hinvT : (N : ℝ)⁻¹ < t₀ / 2)
    (hinvX : (N : ℝ)⁻¹ < x / 2)
    (hinvδ : (N : ℝ)⁻¹ < δ / 3)
    (hs : s ∈ Finset.Ico (gridIndex N t₀) (gridIndex N t)) :
    let k := gridIndex N x + (gridIndex N t - 1 - s)
    let st := (s : ℝ) / (N : ℝ)
    let y := x + t - st
    (st, (k : ℝ) / (N : ℝ)) ∈
        Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ) ∧
      (st, y) ∈ Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ) ∧
      dist (st, (k : ℝ) / (N : ℝ)) (st, y) < δ ∧
      t₀ / 2 * (N : ℝ) ≤ (s : ℝ) ∧
      (s : ℝ) ≤ (t + 1) * (N : ℝ) ∧
      x / 2 * (N : ℝ) ≤ (k : ℝ) ∧ k ≤ R * N := by
  dsimp only
  let k : ℕ := gridIndex N x + (gridIndex N t - 1 - s)
  let st : ℝ := (s : ℝ) / (N : ℝ)
  let y : ℝ := x + t - st
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hstLower, hstUpper, hkLower, hkUpper, hargDist⟩ :=
    floorTransportGeometry N s t₀ t x δ R hN ht₀ ht hx hR
      hinvT hinvX hinvδ hs
  have hstBox : st ∈ Icc (t₀ / 2) (t + 1) :=
    ⟨hstLower, hstUpper.trans (by linarith)⟩
  have hkBox : (k : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) (R : ℝ) := by
    exact ⟨div_nonneg (Nat.cast_nonneg k) hNreal.le,
      (div_le_iff₀ hNreal).2 (by exact_mod_cast hkUpper)⟩
  have hyBox : y ∈ Icc (0 : ℝ) (R : ℝ) := by
    constructor
    · dsimp only [y]
      linarith
    · dsimp only [y]
      have hxtR : x + t ≤ (R : ℝ) := by linarith [hR]
      have hs0 : 0 ≤ st := div_nonneg (Nat.cast_nonneg s) hNreal.le
      linarith
  have hpdist : dist (st, (k : ℝ) / (N : ℝ)) (st, y) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right, dist_nonneg] using hargDist
  have hsLower : t₀ / 2 * (N : ℝ) ≤ (s : ℝ) :=
    (le_div_iff₀ hNreal).mp hstLower
  have hsUpper : (s : ℝ) ≤ (t + 1) * (N : ℝ) :=
    (div_le_iff₀ hNreal).mp hstBox.2
  exact ⟨⟨hstBox, hkBox⟩, ⟨hstBox, hyBox⟩, hpdist,
    hsLower, hsUpper, hkLower, hkUpper⟩

end DerridaRetaux
