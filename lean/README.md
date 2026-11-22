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

## Current status (2026-11-22)

- Project skeleton, toolchain pinned (Lean v4.33.1 + elan), mathlib pinned to
  the archive's rev, oleans fetched: `lake build` completes **clean** -
  zero errors, zero sorries, every build.
- The 14-file abstract cluster lifted with provenance headers; it compiles
  against vanilla mathlib with no archive-internal dependencies.
- **The `ZetaPoleData` discharge is DONE** (see the next section): the
  archive's character-family `PoleData` construction lifted and
  instantiated at the trivial family. Consequently:
  - `zeta_landau_windowed_unconditional` - Rubinstein's windowed Landau
    lemma for zeta, **with no hypotheses at all**;
  - `LandauWindows.t1Soft : T1Soft` - **T1 proved in the soft layer**
    (pure logic from the unconditional lemma).
- **Axiom audit** (`LandauWindows/Axioms.lean`, runs on every build):
  every theorem in the chain - `Deduction.landau_window`,
  `zeta_landau_windowed`, `windowHypU_of_ceiling`, `zetaPoleData`,
  `zeta_landau_windowed_unconditional`, `t1Soft` - depends on exactly
  `[propext, Classical.choice, Quot.sound]` - no `sorryAx`, no extra
  axioms.
- **T1's soft statement** (`LandauWindows/T1.lean`): the certificate data
  (`IsolationRect`), the derived clearance quantities of paper 5.2 as
  explicit definitions (`dbar`, `r_z`, `eps_z`, `D_R`, `D_min`, `r'`,
  `delta'`, `W1`, `W1'`), the validity conditions (V1)-(V5), the certified
  statement (S1), `T1Soft` (now proved), and the certificate reading
  `CeilingRefutesCertificate`.
## The `ZetaPoleData` discharge - DONE (2026-11-22)

The analytic hypothesis bundle is **discharged**, not by re-deriving the
Mellin identity from scratch, but by lifting the archive's own
character-family construction (which builds `PoleData` for any admissible
family, unconditionally, via a dslope-based Mellin transform and mathlib's
zeta-at-1 residue machinery) and instantiating it at the trivial family:

- **Lifted** (provenance headers): `CharFamily.lean` (the family
  structure, `ramp`, `Gchi`, `Gm`), the full `PoleData.lean` (the earlier
  trim restored: `gm`, `zeroSet`, `famD`), and the analytic chain
  `measurableGchi`, `GchiConj`, `GchiGrowth` (the `|Gchi| <= C y^2`
  bound), `mertensUpper` (Mertens-type Lambda/n bounds),
  `mellinGchiOfNeOne` / `mellinGchiModOne` (the Mellin identities),
  `LogDerivLocal`, `LFunctionConj` (conjugation),
  `CharFamilyLFunctionNeZeroOfOneLeRe`, and `PoleDataConstruction.lean`
  (the archive's `poleData.lean`, renamed to avoid a Windows
  case-insensitive filename collision) - culminating in
  `Deduction.poleData F : exists Phi, PoleData (gm F) Phi (zeroSet F)`.
- **Ours** (`Soft/ZetaPoleData.lean`): the trivial family `Ftriv`
  (conductor-1 character alone, weight 1), the bridges
  (`ramp (fun _ => 1) y = (Sz y : C)`, trivial-`Gchi` = `(Gz y : C)`,
  `gm Ftriv = gz`, `zeroSet Ftriv = zetaStripZeros` - using
  `LFunction (1 mod 1) = riemannZeta`, `LFunction_conj`, and mathlib's
  nonvanishing at `1 <= Re`), and the discharge:
  `LandauWindows.zetaPoleData : exists Phi, PoleData gz Phi zetaStripZeros`.

Consequences (all soft layer, all depending on exactly the three standard
Lean axioms, verified on every build):

- `zeta_landau_windowed_unconditional` - **Rubinstein's windowed Landau
  lemma for zeta, with no hypotheses at all**: ceilings
  `Gz x <= C x^theta` on arbitrarily large windows `[Y, Y^(3/2)]` exclude
  zeros with `Re > theta`.
- `LandauWindows.t1Soft : T1Soft` - **T1 proved in the soft layer**, by
  pure logic from the unconditional lemma: a valid certificate + (S1)
  give a zero with `Re > theta`, so ceilings must fail somewhere in
  every window beyond some threshold.

## Not yet done

- The `s0 = -1` mirror direction of `ZetaLandau` (needs the functional
  equation reflection); T1's effective content (explicit constants from
  the paper's Definition 6.1, computed address - the shadow, `Shadow/`);
  the `Y0` in `t1Soft` made explicit.