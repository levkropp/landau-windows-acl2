# lean/ — the formalization (Phase 2)

A Lean 4 project (`lake`), pinned to the Alpöge archive's toolchain and mathlib
(`leanprover/lean4:v4.33.1`, mathlib `0df444a360e…`) so that lifted files compile
against exactly the mathlib they were written for. Build:

```
cd lean
lake update          # fetch mathlib at the pinned rev (once)
lake exe cache get   # download prebuilt mathlib oleans (once, ~4 GB)
lake build           # build this library
```

(elan toolchain required; `lake` auto-installs `leanprover/lean4:v4.33.1` from
the `lean-toolchain` file.)

Two layers, one directory each:

```
lean/
├── LandauWindows.lean           root import
├── LandauWindows/
│   ├── Statement.lean           the statements: Sz, Gz, ZetaLandau — verbatim
│   │                            lifts from the archive's StatementOC/StatementU
│   ├── Soft/                    correctness layer: mathlib-style, classical
│   │                            logic allowed. Currently:
│   │                            • the abstract windowed-Landau cluster, LIFTED
│   │                              from the archive (14 files, provenance
│   │                              headers, imports rewritten; see below),
│   │                              culminating in Deduction.landau_window;
│   │                            • windowHyp.lean: the generic window bridges
│   │                              (lifted, assembled from two archive files);
│   │                            • ZetaWindowed.lean (OURS): the ζ-facing
│   │                              instantiation — windowHypU_of_ceiling,
│   │                              ZetaPoleData (hypothesis-injected analytic
│   │                              content), and zeta_landau_windowed =
│   │                              Rubinstein's windowed Landau lemma for ζ.
│   └── Shadow/    the PA-track artifact: choice-free, witness-explicit,
│                  ℚ-intervals (planned; not started)
```

## What is lifted and what is ours

**Lifted** (`Soft/*.lean`, each file carries a provenance header naming its
source in the archive): the *entire* abstract windowed-Landau machinery —
`PoleData` (the Mellin-transform certificate: measurability, crude growth,
Laplace representation, pole structure), `WindowHypU` (recurring windows with a
ceiling), and the twelve kernel/pole/Cauchy files behind
`Deduction.landau_window`. The lift is mechanical (import paths only; the one
trim is `PoleData.lean`, which drops the archive's character-family-specific
definitions that the abstract theorem does not use). This was possible because
Alpöge's own architecture factors the argument abstractly — the same factoring
our classical paper uses.

**Ours**: `Statement.lean`'s provenance notes, `ZetaWindowed.lean` (the
ζ-instantiation and the windowed statement), and everything in `Shadow/` when
it exists.

## The two-layer discipline

The **soft layer** proves the theorems the way a mathematician would (reals,
`Classical.choice`, mathlib's `riemannZeta`, `vonMangoldt` machinery). It
exists to make correctness easy to audit.

The **shadow** re-proves the same statements with the discipline that makes
PA-strength transfer possible:

| Rule | Rationale |
|---|---|
| no `Classical.choice` / `by classical` in the final path | choice has no computable witness; PA has no choice |
| every `∃` discharged by an explicit computed witness | ACL2 consumes witnesses, not existence proofs |
| reals only via `x ≤ q` / `x ≥ q` with explicit rational `q` and explicit error bounds | ℝ is coded; bounds must be carried |
| no quotients in the statement path | work with explicit representatives |
| termination: every recursion via explicit well-founded measures | mirrors ACL2's admission of total functions |

Success criterion for the shadow: `#print axioms` on its main theorem shows
only the three standard axioms or fewer.

## Hypothesis injection (precedent)

Zero-isolation rectangles and the analytic content enter as **hypotheses**,
never as axioms — the same discipline as the formalized Dudek prime-gap
theorem (Hubbard, arXiv:2611.00157), where the HSW zero-count enters as an
explicit hypothesis. The soft layer's current hypothesis bundle is
`LandauWindows.ZetaPoleData` (Mellin identity, pole structure, crude growth);
discharging it from mathlib's zeta machinery is the next milestone. This keeps
our theorems non-vacuous but assumption-honest, and lets interval-arithmetic
practitioners plug their certificates in.

## Statement hygiene

Lifted statements are kept byte-identical to the archive (modulo the import
line) so that a change of meaning is a one-line diff against the source —
borrowed from IEANTN's design. Before any statement is frozen, diff it against
the archive file named in its header.

## Current status (2026-11-21)

- Project skeleton, toolchain pinned (Lean v4.33.1 + elan), mathlib pinned to
  the archive's rev, oleans fetched: `lake build` completes **clean** —
  zero errors, zero sorries.
- The 14-file abstract cluster lifted with provenance headers; it compiles
  against vanilla mathlib with no archive-internal dependencies.
- `zeta_landau_windowed` **proved** (Rubinstein's windowed Landau lemma for
  ζ, ceiling direction) from the lifted core plus two elementary bridges,
  modulo the single named hypothesis `ZetaPoleData`.
- **Axiom audit** (`LandauWindows/Axioms.lean`, runs on every build):
  `Deduction.landau_window`, `LandauWindows.zeta_landau_windowed`, and
  `LandauWindows.windowHypU_of_ceiling` each depend on exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axioms.
- Not yet done: discharge of `ZetaPoleData` from mathlib's zeta machinery
  (the Mellin identity + pole structure; the next milestone), the
  `s₀ = -1` mirror direction, T1's certificate statement in the soft layer,
  the effective shadow (`Shadow/`).
