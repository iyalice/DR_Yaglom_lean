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
and has been manually checked by the authors. Further revision is planned.
Lean 4 formal verification has not yet been completed. Section 1.5 of the
manuscript describes the use of AI and the current verification status.

**We plan to add the accompanying Lean 4 formalization as soon as possible.**
No Lean development is included in this repository yet, and the current
release does not claim completed formal verification. When the formalization
is added, we will document how to build it, which manuscript results it
covers, and any remaining assumptions or unproved dependencies.

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
