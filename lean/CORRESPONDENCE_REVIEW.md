# Current manuscript correspondence review

Authority: the active root `../DR_Yaglom.tex`; its byte-identical snapshot is
`DR_Yaglom.tex`. `revision-manifest.json` pins the edition, hash, counts and
provenance. The 12 September source, ledgers and reports are archived under
`archive/2026-09-12/`. The current verification outcome is recorded separately
in `validation/2026-09-29/verification-result.json`.

## Changes that require new mathematics

The old `FixedArity.sharpness` disproves the excess limit. The current
`thm:sharpness` disproves the survival limit. Renaming the old theorem would
not establish the new statement. `Sharpness/SurvivalToExcess.lean` proves,
under criticality alone, that the proposed survival limit implies the excess
limit and the logarithmic product exponent two. It uses a finite-mean cutoff,
the exact scalar recurrence, expansive differences and reciprocal barriers.
It does not assume a third tilted moment or import a published input.
`Main/SurvivalSharpness.lean` applies this transfer to the existing explicit
critical power-tail law. The existing real parameter range `0 <= r < 3`,
nonconstant law, finite r-th moment and infinite third moment are retained.
The sole published input in the resulting sharpness theorem is still H3.

The new `lem:productasymptotic` is represented as
`log (criticalProduct n) / log n -> 2`. This is the logarithmic meaning of
`n^(2+o(1))` for a positive product, not a claim that the product divided by
`n^2` converges. Positivity follows from the critical law; the existing
`orbit_criticalProduct_sub_two_log_isLittleO` provides the little-o form.

`prop:far` now has `C(s+1)/N^3`, without a separate bounded error. The new
`farArrivalBoundUniform` absorbs the old bounded error using `s+1 >= 1`.
It retains the exact cutoff and uniform quantifiers.

## Numbered results

The 15 previous numbered results are retained, with the two changes above.
The profile theorem's statement is unchanged. Cubic moments, atom tails,
smoothing, identification, pointwise and arrival bounds, source differences,
spine, third-moment tails, continuum limit, moment/Laplace ODEs and Taylor
remainder have notation or exposition changes without strengthened conclusions.
Every row of `STATEMENT_LEDGER.csv` has refreshed source line ranges.
Inherited inline source-line annotations in the mathematical modules refer to
the archived 12 September snapshot; the current CSV ledgers are authoritative
for current locations and statement meanings. In particular, the legacy
`Main/Sharpness.lean` annotation refers to the old excess conclusion. Existing
Lean APIs and their historical annotations have been retained for traceability.

Seven newly numbered statements are covered as follows:

| Source label | Representation |
| --- | --- |
| `prop:pgf` | Existing exact pgf recursion, propagation of the third moment, criticality, tilted normalization/mean and tilted recursion, collected in one ledger row. |
| `prop:coarse` | Existing coarse excess/product bounds, survival/tilted-mass identities and uniform inverse zero-atom bound. |
| `lem:tiltedlaw` | New coefficientwise probability-law mixture `tiltedLawRecursion`; `drStep` is the independent-copy positive-part law. |
| `lem:transportcoefficients` | Existing positive coefficient, quadratic defect, antitone product and positive product limit. |
| `lem:weightedmass` | New wrapper packages the weighted l1 bound and exact shifted first moment with current quantifiers. |
| `lem:Fmoment` | New wrapper packages the transported mass, moment and cubic tail bounds. |
| `lem:productasymptotic` | New no-third-moment survival-to-product theorem. |

Rows with several declarations represent the components of a bundled paper
statement. A source-level published-input tag may therefore be present even
when a core declaration takes that fact as a hypothesis and has no custom
axioms. The compiled dependency column records the actual axiom set of each
declaration, separately from those source-level tags.

## Labeled and unnumbered formulas

The equation ledger covers all 84 labels beginning `eq:`, `eqn:` or `ineq:`.
Labels with spaces are preserved exactly. Eighteen formerly numbered formulas
remain mapped as unnumbered obligations, so a label deletion does not delete
its proof coverage. The unnumbered ledger retains U01–U62 and adds explicit
rows for the new cutoff, recurrence/barrier, transfer, scale conversion and
cell interpolation arguments, followed by the former equation anchors.

The new allocation identity and predecessor polynomial are already the exact
`cubicAllocation_carrier_identity` and `cubicCarrier_natPred`. The marginal
formula uses the existing infinite-path marginal theorem, not just a finite
sequence of individually specified laws. The transition formula is represented
by the allocation PMF and its pushforward under the positive-part sum; on the
carrier support this is the manuscript's untruncated sum minus one.

The interpolant formula is the four-weight bilinear formula, including mesh
edges. New `RevisionInterpolation.lean` gives spatial and temporal estimates
on closed cells, and converts adjacent-node bounds `C/N` to physical-coordinate
bounds `C`. New `RevisionGridRates.lean` retains the literal logarithmic
smoothing rate on compact time intervals. These are composed with the existing
smoothing theorem in the equation ledger. The existing global compactness proof
uses a weaker square-root modulus, which is sufficient for the same compactness
conclusion; it is not presented as a proof of a logarithmic bound by itself.

The current weak integral identity is covered by
`subsequentialHasWeakEquationOn`. The formal proof obtains it from the
identified profile, whereas the manuscript derives it earlier from the discrete
recursion. This is a difference in proof order, not an additional premise of
the public profile theorem.

## Trust boundary and limits of the review

`HumanInputs.lean` is unchanged byte for byte. H1a/H1b encapsulate the published
coarse estimates, H2 the entrance-string uniqueness implication, and H3 the
stable product estimate. The discussion of the spectral representation and
uniqueness in the paper motivates H2; the spectral theorem is not re-proved in
this project. The Volterra solution equation is explicitly represented and
proved for the constructed string. Definitions and displayed hypotheses (for
example `eq:assumptions` and `eq:survivalassumption`) are mapped as such, not
asserted without their hypotheses.

This review checks mathematical meaning, assumptions, quantifiers, normalization
and changed proof components. Compiler checks certify the Lean declarations;
CSV coverage and this review are not a machine proof of translation from TeX,
nor an independent human peer review. Historical successful logs apply only to
their archived edition; the current result file must report success before the
current edition is described as built and audited.
