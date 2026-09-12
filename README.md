# Exact critical asymptotics for Derrida–Retaux recursions

**Ruiqi Ding, Zehua He, Yutao Liang, Dong Wang, and Yushu Zheng**

This repository contains the manuscript [DR_Yaglom.tex](DR_Yaglom.tex).
It studies the critical Derrida–Retaux recursion with a fixed number of
independent copies, focusing on exact survival asymptotics, the scaling
profile of the tilted distribution, and a geometric conditional limit
under a finite third exponentially tilted moment assumption.

## Lean formalization

The [Lean project](lean/README.md) is now included in `lean/`. The revised project passed a full Lean 4.19.0 build on September 12, 2026: all 283 root-project modules, 419 source-ledger declarations, and 382 additional axiom-audit declarations passed their respective checks.

The formalization accepts exactly four published inputs, isolated in [HumanInputs.lean](lean/DerridaRetaux/HumanInputs.lean). The main profile theorem depends on H1a/H1b/H2; the sharpness theorem depends on H3. See [EXTERNAL_INTERFACES.md](lean/EXTERNAL_INTERFACES.md) for their exact signatures and scope, and [AcceptanceReport.md](lean/AcceptanceReport.md) for the verification report. No Comparator verification is claimed.

With elan installed, build from the repository root:

```sh
cd lean
lake exe cache get
lake build
```

The three correspondence ledgers and reproducible audit scripts are included in `lean/`. The latest build and audit evidence is in [lean/validation/2026-09-12](lean/validation/2026-09-12).

## Manuscript provenance

The authors' current manuscript records their manual checking of the mathematical arguments. Further revision is planned. The root `DR_Yaglom.tex` is preserved as published; its statement that Lean verification was not yet complete predates the completed build reported above.

`lean/DR_Yaglom.tex` is the exact frozen source used for the formalization, with SHA-256 `652c080e30cfc8cb37ea9636ae74e4c0b30875e1a69db5ae81008137b5a0b82a`. At this upload, it differs from the root manuscript only in the AI/manual-review disclosure paragraph; the mathematical text is unchanged. Keeping this snapshot preserves the source hashes and line references in the audit.

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
