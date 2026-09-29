# Current manuscript verification report — 29 September 2026

The current edition passed `lake build`, the audit-dependency build, the
compiled declaration/axiom audit, and the source/ledger checks. No proof
placeholder, unsafe declaration, foreign project import, or unapproved custom
axiom was found. The four published input declarations are unchanged.

The manuscript disclosure was subsequently shortened as an editorial change.
The mathematical text and all Lean sources are unchanged; the compiled logs
and machine result retain their original input hashes. Current snapshot and
ledger locations were refreshed separately; see the
[editorial refresh record](validation/2026-09-29/editorial-disclosure/refresh.json).

## Source identity and coverage

- Authority: [active manuscript](../DR_Yaglom.tex), byte-identical to
  [the Lean snapshot](DR_Yaglom.tex).
- Manuscript SHA-256: `c4e796e0161cff5420fff55cb2ed00c13bca4bbac9038d7a7fa11f2c969eeff2`.
- Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- 22 numbered results, 84 labeled formulas, and
  85 unnumbered ledger items.
- 457 unique source-ledger declarations;
  624 unique declarations in the consolidated
  audit, including the extended audit set.

The new survival sharpness conclusion is `FixedArity.sharpnessSurvival`.
The no-third-moment survival-to-excess/product transfer is proved in
`Sharpness/SurvivalToExcess.lean`; the legacy excess counterexample remains an
ingredient. Updated statement wrappers, closed-cell interpolation and literal
logarithmic grid rates are included in the root import.

## Exact public custom-axiom dependencies

| Declaration | Published inputs |
| --- | --- |
| `FixedArity.profile` | H1a, H1b, H2 |
| `FixedArity.sharpnessSurvival` | H3 |
| `FixedArity.productAsymptoticOfSurvival` | none |
| `excess_tendsto_of_survival_asymptotic` | none |
| `FixedArity.cubicWeightedInfiniteChain` | none |
| `FixedArity.momentLaplaceLocalIntegralDerivatives` | H1a, H1b |
| `FixedArity.farArrivalBoundUniform` | H1a, H1b |
| `FixedArity.tiltedLawRecursion` | none |
| `FixedArity.weightedMass` | H1a, H1b |
| `FixedArity.arrivalMomentTail` | H1a, H1b |

These sets come from fresh `#print axioms` output. Standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound` are permitted separately.
Core declarations may take a published fact as an explicit hypothesis;
the ledgers retain source-level input tags as well as the actual per-declaration
compiled dependency sets. The exact external signatures remain in
[EXTERNAL_INTERFACES.md](EXTERNAL_INTERFACES.md).

## Reproducible evidence

- [Machine result and hashes](validation/2026-09-29/verification-result.json).
- [Project build](validation/2026-09-29/build.log).
- [Audit dependency build](validation/2026-09-29/audit-dependency-build.log).
- [Full theorem types and axiom output](validation/2026-09-29/compiled-axioms.log).
- [Source and ledger checks](validation/2026-09-29/source-and-ledger-check.log).
- [Semantic correspondence review](CORRESPONDENCE_REVIEW.md).

Run `python3 scripts/verify_all.py` from this directory to reproduce the gate.
Dependency artifacts were restored from the cache for the pinned versions;
this was a full project target build, not a claim of recompiling mathlib from
scratch. The earlier interrupted baseline attempt is not acceptance evidence.
The September 12 report and snapshot are preserved under
[archive/2026-09-12](archive/2026-09-12/).

## Scope

The formal results are conditional on H1a/H1b/H2/H3 where listed. Those
published theorems are not re-proved here. A compiler-checked Lean statement
and a reviewed TeX correspondence are different kinds of evidence: the latter
is not a machine-checked translation or independent human peer review.
Compound mappings and differences in proof order are documented explicitly in
the correspondence review. No Comparator verification is claimed.
