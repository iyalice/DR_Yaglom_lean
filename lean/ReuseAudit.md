# Reuse provenance for the current edition

The current project starts from the complete `lean/` directory of
`iyalice/DR_Yaglom_lean` commit
`2830c58dee0265b8cc71b0dc16acc944cda316a2`.
The original reuse analysis is retained at
[archive/2026-09-12/ReuseAudit.md](archive/2026-09-12/ReuseAudit.md); its historical
claims apply to that earlier delivery, not to newly written code.

The update adds five mathematical modules: survival-to-excess transfer,
survival sharpness, current-statement wrappers, closed-cell interpolation,
and logarithmic grid rates. Existing definitions and theorem signatures are
preserved; the previous sharpness theorem remains an ingredient. There are no
imports from other local Derrida–Retaux projects and no added Lake dependency.
The four published external inputs remain byte-identical.

Dependency artifacts were restored for the pinned Lean/mathlib version.
Reused compiled artifacts are not treated as new proof evidence: the current
acceptance requires the project build and a fresh compiled declaration audit.
