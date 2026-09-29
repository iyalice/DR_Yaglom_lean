# Exact critical asymptotics for Derrida–Retaux recursions

**Ruiqi Ding, Zehua He, Yutao Liang, Dong Wang, and Yushu Zheng**

This repository contains the manuscript [DR_Yaglom.tex](DR_Yaglom.tex).
It studies the critical Derrida–Retaux recursion with a fixed number of
independent copies, focusing on exact survival asymptotics, the scaling
profile of the tilted distribution, and a geometric conditional limit
under a finite third exponentially tilted moment assumption.

## Current status

This is a preliminary research draft, shared to provide a dated record of
the work. The mathematical proof draft was generated with AI assistance
and has been manually checked by the authors, who take responsibility for
its content. Section 1.5 of the manuscript describes the use of AI and the
current verification status.

## Lean formalization and scope

The updated formalization is included in [lean/](lean/README.md), alongside
its current manuscript snapshot, correspondence ledgers and verification
records. It passed a Lean 4.19.0 project build and compiled axiom audit on
September 29, 2026. The current ledgers cover 22 numbered results, 84 labeled
formulas and 85 unnumbered obligations, mapping to 457 unique declarations.
The compiled audit also covers the supplementary declaration checks and
the four published-input declarations themselves. See [AcceptanceReport.md](lean/AcceptanceReport.md).

The public results include `FixedArity.profile` and the current Appendix A
survival counterexample `FixedArity.sharpnessSurvival`. The new
`productAsymptoticOfSurvival` proves the required product exponent from the
survival limit without a third-moment assumption. The earlier excess
sharpness theorem is retained as a proved ingredient.

Four published inputs remain declared as axioms: two CDHLS estimates,
Kotani inverse uniqueness, and the Chen–Shi stable-product estimate.
The profile theorem uses the first three; survival sharpness uses the fourth.
The survival-to-excess/product transfer has no custom axiom. Exact signatures
and dependencies are documented in
[EXTERNAL_INTERFACES.md](lean/EXTERNAL_INTERFACES.md) and the compiled audit.
No new external input was added in this update.

The [correspondence review](lean/CORRESPONDENCE_REVIEW.md) explains compound
statement mappings, interpolation estimates and proof-order differences.
Compilation verifies Lean statements relative to the declared inputs;
the TeX-to-Lean correspondence is not itself machine-checked, and these
checks are not independent human peer review.

To reproduce the build and audit:

```sh
cd lean
lake exe cache get
python3 scripts/verify_all.py
```

The toolchain and dependencies are pinned. See the
[Lean README](lean/README.md) for the macOS cache alternative. The original
September 12 source and reports are preserved in
[lean/archive/2026-09-12](lean/archive/2026-09-12/).

## Building the manuscript

With a LaTeX installation providing `amsart` and `mathpazo`, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error DR_Yaglom.tex
pdflatex -interaction=nonstopmode -halt-on-error DR_Yaglom.tex
```

This produces `DR_Yaglom.pdf`. The bibliography is included in the TeX
source, so no separate bibliography command is needed. Generated PDFs,
logs, and auxiliary files are excluded from version control.

Comments, corrections, and suggestions are welcome through GitHub issues.
