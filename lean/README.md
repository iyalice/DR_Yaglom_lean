# Derrida–Retaux formalization for the current manuscript

This directory contains the Lean 4 formalization corresponding to the active
[manuscript](../DR_Yaglom.tex). Its local [snapshot](DR_Yaglom.tex) must be
byte-identical to that source. The toolchain remains Lean 4.19.0 and mathlib is
locked to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The current edition passed the full project build, compiled axiom audit and
source/ledger checks on 29 September 2026. See [AcceptanceReport.md](AcceptanceReport.md).

The update starts from [DR_Yaglom_lean, commit 2830c58](https://github.com/iyalice/DR_Yaglom_lean/tree/2830c58dee0265b8cc71b0dc16acc944cda316a2/lean).
The earlier source, ledgers and reports are retained under
[archive/2026-09-12](archive/2026-09-12/). Earlier build logs certify that edition
only. The outcome of the current build and audit is recorded in
[verification-result.json](validation/2026-09-29/verification-result.json).

## Public results and changes

- `DerridaRetaux.FixedArity.profile`: the profile theorem and all its stated
  survival, moment, atom and conditional-law consequences.
- `DerridaRetaux.FixedArity.sharpnessSurvival`: the current Appendix A
  counterexample to the exact survival asymptotic for every real `0 <= r < 3`.
- `DerridaRetaux.FixedArity.productAsymptoticOfSurvival`: criticality and the
  proposed survival limit imply logarithmic product exponent two, without a
  third-moment assumption.
- `DerridaRetaux.FixedArity.farArrivalBoundUniform`: the revised uniform far
  estimate; the tilted-law, weighted-mass and arrival-moment wrappers are in
  [RevisionStatements.lean](DerridaRetaux/Main/RevisionStatements.lean).
- Closed-cell interpolation and logarithmic grid-scale bounds are in
  [RevisionInterpolation.lean](DerridaRetaux/Analysis/RevisionInterpolation.lean)
  and [RevisionGridRates.lean](DerridaRetaux/Analysis/RevisionGridRates.lean).

The legacy excess sharpness theorem is retained as a proved ingredient.
The current survival conclusion uses a newly proved transfer theorem; it is
not obtained merely by renaming the legacy declaration.

## Reproduce verification

From this directory, with elan installed:

```sh
lake exe cache get
python3 scripts/verify_all.py
```

The script runs `lake build`, builds the audit dependency, compiles the union
of source and extended declaration audits, rejects unapproved axioms, checks
exact dependency sets of the public results, and refreshes the per-declaration
CSV dependency fields only from successful compiler output. It records source
and log hashes and refuses a success result if the source changes during the
run. For source-only checking after a successful audit:

```sh
python3 scripts/verify_revision.py
```

If the macOS native cache executable has a dynamic-loader error, use:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

An interrupted or mixed dependency cache can be restored from downloaded cache
archives with `lake env lean --run .lake/packages/mathlib/Cache/Main.lean unpack!`.
Build products and `.lake/` are excluded from version control.

## Correspondence and trust

The current ledgers contain [22 numbered results](STATEMENT_LEDGER.csv),
[84 labeled formulas](EQUATION_LEDGER.csv), and
[85 unnumbered obligations](UNNUMBERED_LEDGER.csv), mapping to 457 unique Lean
declarations. See [CORRESPONDENCE_REVIEW.md](CORRESPONDENCE_REVIEW.md) for changed
statements, compound mappings, the treatment of interpolation, and proof-order
differences.

[HumanInputs.lean](DerridaRetaux/HumanInputs.lean) is unchanged. It declares four
published external inputs: H1a/H1b (CDHLS), H2 (Kotani), and H3 (Chen–Shi).
They are accepted premises, not re-proved in this project. The profile branch
uses H1a/H1b/H2; survival sharpness uses H3. The survival-to-excess/product
transfer requires no custom axiom. Exact interfaces are documented in
[EXTERNAL_INTERFACES.md](EXTERNAL_INTERFACES.md).

Compilation verifies Lean statements relative to these premises. The
TeX-to-Lean correspondence review is not a machine-checked translation or an
independent human peer review. No Comparator verification is claimed.
