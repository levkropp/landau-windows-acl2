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
- **T1's soft statement landed** (`LandauWindows/T1.lean`): the certificate
  data (`IsolationRect`), the derived clearance quantities of paper §5.2 as
  explicit definitions (`dbar`, `r_z`, `eps_z`, `D_R`, `D_min`, `r'`,
  `delta'`, `W1`, `W1'`), the validity conditions (V1)–(V5), the certified
  statement (S1), and `T1Soft` in the logical shape fixed by
  `docs/statement.md` §3. Statement only — the target the proof work aims
  at; the explicit constants (paper Definition 6.1) and the computed
  address are the effective content for `Shadow/`.
- **`MellinRamp.lean` lifted** (the ramp-integral Mellin identity) — the
  first brick of the `ZetaPoleData` discharge.

## The `ZetaPoleData` discharge plan (recon done, 2026-11-22)

Mathlib at our pin has the decisive lemma:
`Mathlib.NumberTheory.LSeries.Dirichlet.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
— the identity `LSeries vonMangoldt s = −deriv riemannZeta s / riemannZeta s`
for `1 < s.re`, plus `LSeriesSummable_vonMangoldt` (summability), and even
the Dirichlet-character twists (future T1-L). Combined with the lifted
`mellin_ramp`, the plan per `PoleData` field:

1. `meas`, `growth` — elementary: piecewise measurability of the Λ-sums;
   `|Gz x| ≤ K x log²x` from `vonMangoldt ≤ log` + harmonic-log sums.
2. `laplace` — the Mellin identity of paper Prop 2.2 for `2 < Re s`:
   `mellin_ramp` + the Tonelli interchange (summability from
   `LSeriesSummable_vonMangoldt`) + the
   `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` identity + the
   `u = log x` substitution, plus the elementary transforms of the
   `x log x` and `(1+γ)x` terms.
3. `diff`, `pole` — restate `Fz` as the meromorphic expression
   `−ζ'/ζ(s)/(s(s−1)) − 1/(s−1)² + (1+γ)/(s−1)` (junk outside its
   convergence set is harmless for `DifferentiableOn`); poles exactly at
   the zeros with residues `−ν/(ρ(ρ−1))` via mathlib's order-of-zero API.
   The delicate point: `s = 1`, where ζ's pole must cancel against the
   correction terms (needs ζ's Laurent data at 1 — to be sourced from
   mathlib's L-series work or derived).
4. `iso` — mathlib's isolation/countability of zero sets of analytic
   functions.
5. `pos` — definitional for our `zetaStripZeros`.

## Not yet done
