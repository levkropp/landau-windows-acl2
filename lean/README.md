# lean/ — the formalization (Phase 2)

Planned Lean 4 project against mathlib. Two layers, one directory each:

```
lean/
├── LandauWindows/
│   ├── Soft/      correctness layer: mathlib-style, classical logic allowed
│   └── Shadow/    the PA-track artifact: choice-free, witness-explicit, ℚ-intervals
```

## The two-layer discipline

The **soft layer** proves the theorems the way a mathematician would (reals, `Classical.choice`, mathlib's `riemannZeta`, `vonMangoldt` machinery). It exists to make correctness easy to audit.

The **shadow** re-proves the same statements with the discipline that makes PA-strength transfer possible:

| Rule | Rationale |
|---|---|
| no `Classical.choice` / `by classical` in the final path | choice has no computable witness; PA has no choice |
| every `∃` discharged by an explicit computed witness | ACL2 consumes witnesses, not existence proofs |
| reals only via `x ≤ q` / `x ≥ q` with explicit rational `q` and explicit error bounds | ℝ is coded; bounds must be carried |
| no quotients in the statement path | work with explicit representatives |
| termination: every recursion via explicit well-founded measures | mirrors ACL2's admission of total functions |

Mathlib already provides the substrate: `riemannZeta` (definition, functional equation, `riemannZeta_ne_zero_of_one_le_re`), `ArithmeticFunction.vonMangoldt`, `RiemannHypothesis` (statement), Dirichlet characters and L-functions (Loeffler–Stoll). What mathlib does *not* have — and what we must build — is everything Mellin/high-derivative on the way to the windowed criterion.

## Hypothesis injection (precedent)

Zero-isolation rectangles enter as **hypotheses**, never as axioms — the same discipline as the formalized Dudek prime-gap theorem (Hubbard, arXiv:2611.00157), where the HSW zero-count enters as an explicit hypothesis. This keeps our theorems non-vacuous but assumption-honest, and lets interval-arithmetic practitioners plug their certificates in.

## Statement hygiene

Statements get fingerprints (structure-hash) so that a change of meaning is a one-line diff — borrowed from IEANTN's design. The final target statements should be compared against the Alpöge archive's `ZetaLandau` / windowed variants line-by-line before being frozen.
