# External interfaces

Freeze status: **COMPLETE -- exactly four primitive declarations**.
On 2026-09-10 the user explicitly approved correcting the ENNReal right-boundary target from `Filter.atTop` to the topological neighborhood `(𝓝 ⊤)`. This is the literal encoding of `M(0-) = ∞`; all other H2 hypotheses and its conclusion are unchanged.

The user approved the exact transparent definition of
`IsEntranceNormalizedVolterraSolution`.  All definitions needed by the four contracts
now compile, the fact types are frozen in `DerridaRetaux/ExternalSignatures.lean`, and
the primitive wrappers are isolated in `DerridaRetaux/HumanInputs.lean`.

SHA-256 of the frozen `HumanInputs.lean`:
`2f35158a78164c7ffe0e8def2049a5c6c9a747fa3671b38965110677752f465e`.

## Shared transparent definitions

The two source families use one half-open product convention:

```lean
def tiltedPartition (m : ℕ) (p : ProbabilityMass) : ℝ :=
  tiltedMoment m 0 p

def criticalProduct (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n,
    tiltedPartition m (orbit m p₀ j) ^ (m - 1)
```

Thus `criticalProduct m p₀ 0 = 1`; CDHLS's inclusive product through `G_n` is
`criticalProduct m p₀ (n + 1)`, whereas Chen--Shi's product through `G_(n-1)` is
`criticalProduct m p₀ n`.

The approved Volterra and characteristic relations are transparent definitions in
`DerridaRetaux/Rigidity/EntranceStringBase.lean`; their exact expansions are recorded
in `BLOCKERS.md`.  They contain no theorem field or target conclusion.

## H1a -- CDHLS Theorem 3, upper half

The compiled transparent fact type is:

```lean
def CDHLSExcessFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (_hm : 2 ≤ m)
    (_hcrit : Critical m p₀)
    (_hthird : TiltSummable m 3 p₀)
    (_hnonconstant : ¬ IsDirac p₀) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      tiltedPartition m (orbit m p₀ n) - 1 ≤ C / (n : ℝ)
```

The exact primitive declaration is:

```lean
axiom cdhls_excess_upper
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant
```

Primary source: [CDHLS, arXiv:1705.04787v2](https://arxiv.org/pdf/1705.04787v2),
Theorem 3.  The published lower excess bound is excluded.  Conversion to the
manuscript's `C / (n + 1)` form, including generation zero, remains internal.

## H1b -- CDHLS Proposition 1, inclusive endpoint

```lean
def CDHLSProductFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (_hm : 2 ≤ m)
    (_hcrit : Critical m p₀)
    (_hnonconstant : ¬ IsDirac p₀) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      criticalProduct m p₀ (n + 1) ≤ C * (n : ℝ) ^ 2

axiom cdhls_product_upper
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    CDHLSProductFact m p₀ hm hcrit hnonconstant
```

Primary source: [CDHLS, arXiv:1705.04787v2](https://arxiv.org/pdf/1705.04787v2),
Proposition 1.  The `n + 1` in the half-open project notation records the source's
inclusive endpoint.  No third-moment hypothesis belongs in H1b.

## H2 -- Kotani characteristic equality to translation

```lean
def KotaniCharacteristicFact
    (M₁ M₂ : EntranceString)
    (h₁ h₂ : ℝ → ℝ)
    (_hentrance₁ : IsEntranceType M₁)
    (_hentrance₂ : IsEntranceType M₂)
    (_hsecond₁ : HasSecondEntranceMoment M₁)
    (_hsecond₂ : HasSecondEntranceMoment M₂)
    (_hright₁ : HasRightEnd M₁ 0)
    (_hright₂ : HasRightEnd M₂ 0)
    (_hcharacteristic₁ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₁ lambda (h₁ lambda))
    (_hcharacteristic₂ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₂ lambda (h₂ lambda))
    (_hequal : ∀ lambda : ℝ, lambda < 0 → h₁ lambda = h₂ lambda) : Prop :=
  ∃ c : ℝ, ∀ x : ℝ,
    stringCumulative M₁ (x + c) = stringCumulative M₂ x

axiom kotani_characteristic_eq_implies_translate
    (M₁ M₂ : EntranceString)
    (h₁ h₂ : ℝ → ℝ)
    (hentrance₁ : IsEntranceType M₁)
    (hentrance₂ : IsEntranceType M₂)
    (hsecond₁ : HasSecondEntranceMoment M₁)
    (hsecond₂ : HasSecondEntranceMoment M₂)
    (hright₁ : HasRightEnd M₁ 0)
    (hright₂ : HasRightEnd M₂ 0)
    (hcharacteristic₁ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₁ lambda (h₁ lambda))
    (hcharacteristic₂ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₂ lambda (h₂ lambda))
    (hequal : ∀ lambda : ℝ, lambda < 0 → h₁ lambda = h₂ lambda) :
    KotaniCharacteristicFact M₁ M₂ h₁ h₂ hentrance₁ hentrance₂ hsecond₁ hsecond₂
      hright₁ hright₂ hcharacteristic₁ hcharacteristic₂ hequal
```

Primary source: [Kotani, arXiv:1304.6786v1](https://arxiv.org/pdf/1304.6786v1),
Theorem 1 together with the characteristic-to-spectral implication explicitly bundled
by the handoff.  H2 is one composite primitive; it is not split.  Its premises retain
two entrance strings, second entrance moments, common right endpoint zero, and equal
characteristics for every negative parameter.  It stops at translation equivalence.
Concrete string construction, characteristic witnesses, endpoint de-translation, and
every profile conclusion remain internal.

## H3 -- Chen--Shi stable-product bound

```lean
def ChenShiStableProductFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (alpha c₀ : ℝ)
    (_hm : 2 ≤ m)
    (_halpha : 2 < alpha ∧ alpha < 4)
    (_hc₀ : 0 < c₀)
    (_hcrit : Critical m p₀)
    (_htail :
      Tendsto
        (fun k : ℕ ↦ p₀.mass k * (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
        Filter.atTop (𝓝 c₀)) : Prop :=
  ∃ c₁ c₂ : ℝ,
    0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ n : ℕ, 1 ≤ n →
        c₁ * Real.rpow (n : ℝ) (alpha - 2) ≤ criticalProduct m p₀ n ∧
          criticalProduct m p₀ n ≤ c₂ * Real.rpow (n : ℝ) (alpha - 2)

axiom chenShi_stable_product
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (alpha c₀ : ℝ)
    (hm : 2 ≤ m)
    (halpha : 2 < alpha ∧ alpha < 4)
    (hc₀ : 0 < c₀)
    (hcrit : Critical m p₀)
    (htail :
      Filter.Tendsto
        (fun k : ℕ ↦ p₀.mass k * (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
        Filter.atTop (𝓝 c₀)) :
    ChenShiStableProductFact m p₀ alpha c₀ hm halpha hc₀ hcrit htail
```

Primary source: [Chen--Shi, arXiv:2006.06140v1](https://arxiv.org/pdf/2006.06140v1),
assumption (1.4) and Theorem 1.1.  The tail is for the original law, the exponent is
`alpha - 2`, and the product is half-open.  There is no artificial above-one premise
and no tilted-law tail substitution.

## Source hypotheses and dependency firewall

| Input | Retained source hypotheses | Deliberately excluded | May reach |
| --- | --- | --- | --- |
| H1a | fixed `m >= 2`, criticality, finite third tilted moment, non-Dirac law | lower excess bound | profile branch |
| H1b | fixed `m >= 2`, criticality, non-Dirac law, inclusive product endpoint | third-moment premise | profile branch |
| H2 | two entrance strings, second entrance moments, right endpoint zero, equal negative-axis characteristics | concrete string/profile conclusion | rigidity call only |
| H3 | original-law tail, `2 < alpha < 4`, `c₀ > 0`, criticality | above-one premise or tilted tail | sharpness only |

- `ExternalSignatures.lean` contains only the four transparent fact types.
- `HumanInputs.lean` contains exactly the four axioms shown above and no fifth
  primitive.
- Axiom-free core modules do not import `HumanInputs.lean`; source-facing `Main/*` wrappers
  invoke only their declared published facts, and the root intentionally exports those wrappers.
- `FixedArity.cubicMoment` invokes only H1b, and
  `FixedArity.firstTiltedAtomTail` invokes only H1a.  Their recurrence, positivity,
  low-moment, transport-product, and tail proofs live in axiom-free core modules.
- `FixedArity.sharpness_core` receives a Chen--Shi fact as an explicit proof
  parameter and imports no human input.  The proved `FixedArity.sharpness` wrapper
  invokes only H3 and does not import the profile theorem.
- The profile core receives H1a, H1b, and H2 as three explicit proof parameters;
  `FixedArity.profile` is the thin final wrapper invoking exactly those inputs.
- Old DR external records and target-equivalent conclusions remain forbidden imports.

The interface remains frozen in the current manuscript update. Current coverage
is recorded by the 22-result, 84-equation and 85-item unnumbered ledgers.
The earlier completion record is archived under `archive/2026-09-12/`.

`FixedArity.sharpnessSurvival` adds the current survival conclusion by using
the no-third-moment theorem `excess_tendsto_of_survival_asymptotic` before
applying the legacy excess counterexample. This introduces no new published
input. The current compiled audit checks exact dependency sets for the profile,
survival sharpness and transfer theorems; see
`validation/2026-09-29/verification-result.json` for its outcome and the CSV
columns for exact per-declaration sets.
