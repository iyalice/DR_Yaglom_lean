# Exact critical asymptotics for Derrida–Retaux recursions

**Ruiqi Ding, Zehua He, Yutao Liang, Dong Wang, and Yushu Zheng**

This repository contains the [manuscript](DR_Yaglom.tex) and its Lean 4 formalization. The paper studies critical Derrida–Retaux recursions with fixed arity, their scaling profile and consequences, and the sharpness of the moment threshold.

## Verification status

The revised project passed a full Lean 4.19.0 build on September 12, 2026. Its 419 source-ledger declarations and 382 additional audit declarations were checked for axiom dependencies. There are no proof placeholders in the delivered project source.

The formalization is conditional on four explicitly declared published inputs in [HumanInputs.lean](DerridaRetaux/HumanInputs.lean): H1a and H1b (CDHLS), H2 (Kotani), and H3 (Chen–Shi). The main profile theorem uses H1a/H1b/H2; the sharpness theorem uses H3. These external results are accepted premises, not re-proved here. See [EXTERNAL_INTERFACES.md](EXTERNAL_INTERFACES.md) for their exact scope.

The manuscript records the provenance of its AI-assisted draft. Lean compilation and axiom auditing do not by themselves establish that every natural-language statement has been represented correctly, nor constitute independent human peer review. No Comparator verification is claimed.

## Main declarations

- `DerridaRetaux.FixedArity.profile` — [ProfileTheorem.lean](DerridaRetaux/Main/ProfileTheorem.lean).
- `DerridaRetaux.FixedArity.sharpness` — [Sharpness.lean](DerridaRetaux/Main/Sharpness.lean).
- `DerridaRetaux.FixedArity.cubicWeightedInfiniteChain` — [InfinitePath.lean](DerridaRetaux/Spine/InfinitePath.lean).
- `DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives` — [MomentLaplaceRegularity.lean](DerridaRetaux/Main/MomentLaplaceRegularity.lean).

## Build

Install Lean through elan, then run from this directory:

```sh
lake exe cache get
lake build
```

The toolchain is pinned to Lean 4.19.0. Mathlib is pinned to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; other dependencies are locked in `lake-manifest.json`. Do not update these versions merely to reproduce the reported build.

If the native cache executable fails with a macOS dynamic-loader error, the same cache tool can be run through Lean:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

## Source correspondence and audits

- [STATEMENT_LEDGER.csv](STATEMENT_LEDGER.csv): 15 numbered results.
- [EQUATION_LEDGER.csv](EQUATION_LEDGER.csv): 82 labeled equations.
- [UNNUMBERED_LEDGER.csv](UNNUMBERED_LEDGER.csv): U01–U62.
- [AcceptanceReport.md](AcceptanceReport.md): verification scope and exact public theorem types.
- [DEPENDENCY_DAG.md](DEPENDENCY_DAG.md): dependency structure.
- [ReuseAudit.md](ReuseAudit.md): reuse provenance.

The CSV ledgers include exact per-declaration custom-axiom dependencies. Detailed historical logs referenced by the report are distributed in the complete verification delivery archive accompanying this source distribution.

To repeat source checks and the declaration audit:

```sh
python3 scripts/verify_revision.py
bash scripts/verify_ledgers.sh
lake build DerridaRetaux.Audit.ArchitectureCounterexample
lake env lean DerridaRetaux/Audit/AllSourceDecls.lean
lake env lean DerridaRetaux/Audit/StatementCompletion.lean
lake env lean DerridaRetaux/Audit/PrintAxioms.lean
```

## Manuscript

The verified source is `DR_Yaglom.tex`, SHA-256 `652c080e30cfc8cb37ea9636ae74e4c0b30875e1a69db5ae81008137b5a0b82a`. Compile it with `pdflatex` twice. Generated files and `.lake/` are excluded from version control.
