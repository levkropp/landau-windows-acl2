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
source in the archive): the *entire* windowed-Landau cluster of the archive's
`DedekindLFunctions` tree - now including the character-family side.
Concretely: the abstract core (`PoleData` restored in full, `WindowHypU`, and
the twelve kernel/pole/Cauchy files behind `Deduction.landau_window`), the
character-family construction (`CharFamily`, `PoleDataConstruction` - the
archive's `poleData.lean`, renamed for a Windows case-insensitive filename
collision - plus the analytic chain: `measurableGchi`, `GchiConj`,
`GchiGrowth`, `mertensUpper`, `mellinGchiOfNeOne`, `mellinGchiModOne`,
`LogDerivLocal`, `LFunctionConj`, `CharFamilyLFunctionNeZeroOfOneLeRe`), and
the family-level finale (`WindowHypOfRpow`, `WindowHypUOfWindowHyp` - both in
full, replacing an earlier partial lift `windowHyp.lean` - `lemmaL`,
`ZeroFreeOfRpowWindow`: windowed ceilings on the family statistic give
zero-freeness for every character of the family, unconditionally).  The lift
is mechanical (import paths only).  Every `LandauTheorems` file of the archive
is lifted except the `Ch*`/`SplitInertia`/`RunBase...` files, which are the
archive's step-3 arithmetic core (constructing the even-character family and
its ceiling) and deliberately out of scope for this step-2 project.

**Ours**: `Statement.lean`'s provenance notes, `ZetaWindowed.lean` (the
zeta-instantiation and the windowed statement), `ZetaPoleData.lean` (the
trivial-family discharge), `ZetaLandau.lean` (the mirror direction and the
full archive statements), `T1.lean`, `Axioms.lean`, and everything in
`Shadow/` when it exists.
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
- **The archive's tail is lifted** (`WindowHypOfRpow` and
  `WindowHypUOfWindowHyp` in full - replacing the earlier partial lift
  `windowHyp.lean` - plus `lemmaL` and `ZeroFreeOfRpowWindow`): the
  family-level windowed Landau lemma
  `Deduction.zeroFree_of_rpow_window` is now available verbatim from the
  archive.
- **The mirror (`s0 = -1`) direction is DONE modulo one named input**
  (see the section after next): `zeta_landau : Formalism.ZetaLandau`
  (both signs) and `zeta_landau_eps : Formalism.ZetaLandauEps` are
  **proved**, the floor direction reduced to the single named classical
  input `ZetaNoRealStripZeros`.
- **Axiom audit** (`LandauWindows/Axioms.lean`, runs on every build):
  every theorem in the chain - `Deduction.landau_window`,
  `Deduction.lemmaL`, `Deduction.zeroFree_of_rpow_window`,
  `zeta_landau_windowed`, `windowHypU_of_ceiling`, `zetaPoleData`,
  `zeta_landau_windowed_unconditional`, `t1Soft`, `poleData_neg`,
  `zeta_landau_windowed_floor`, `zeta_landau`, `zeta_landau_eps` -
  depends on exactly `[propext, Classical.choice, Quot.sound]` - no
  `sorryAx`, no extra axioms.
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

## The mirror direction (`s0 = -1`) - DONE modulo one named input (2026-11-22)

`Formalism.ZetaLandau` (the archive's statement) is one-sided in TWO
senses: the bound `s0 * Gz x <= C x^theta` may hold with either sign
`s0 in {1, -1}`.  The `s0 = 1` (ceiling) direction is the one the windowed
machinery proves; the `s0 = -1` (mirror, floor) direction is NOT more of
the same - it cannot be obtained by the functional equation (the FE maps
zeros to reflected zeros, but the statement is about the SAME right half
plane, and a real strip zero would contribute a *positive* growing term
to `Gz`, invisible to any floor bound).  The correct route is that a floor
on `Gz` is a ceiling on `-Gz`, so `Deduction.landau_window` applies to the
NEGATED statistic:

- `poleData_neg` (ours, `Soft/ZetaLandau.lean`): `PoleData g Phi Z` passes
  to `(fun u => -g u, fun s => -Phi s)` provided `Z` has no real points.
  Every field is linearity except `pole`: the residue at a zero is negated,
  and at a REAL zero the `pole` field demands a *positive real* residue -
  which is exactly the mathematical content (a positive-residue pole grows
  upward and cannot contradict a floor).  Away from the real axis only
  nonvanishing of the residue is needed, and the windowed contradiction is
  a magnitude argument.
- `ZetaNoRealStripZeros` (ours): the single named classical input - zeta
  has no real zeros in the open strip `(0,1)`, classically because
  `zeta(sigma) < 0` there.  This is the same fact the classical proof of
  the one-sided theorem uses (see ../docs/statement.md section 1, whose
  auxiliary `H` is holomorphic on the real axis precisely because of it).
- `zeta_landau_windowed_floor` (ours): the windowed mirror lemma - floors
  `-Gz x <= C x^theta` on arbitrarily large windows exclude zeros with
  real part `> theta`, given `ZetaNoRealStripZeros`.
- `windowed_of_eventual` (ours): an eventual one-sided bound holds
  throughout every sufficiently large window (the classical statements
  are eventual, the machinery windowed).
- `zeta_landau : Formalism.ZetaLandau` and
  `zeta_landau_eps : Formalism.ZetaLandauEps` (ours): the archive's
  statement-level targets, both signs, proved.

### Discharge plan for `ZetaNoRealStripZeros`

Mathlib at our pin has: the Laurent data at 1
(`riemannZeta_residue_one`, `riemannZeta_eq_inv_sub_add` with an entire
remainder `riemannZeta1`), the functional equation
(`riemannZeta_one_sub`), nonvanishing at `1 <= re`
(`riemannZeta_ne_zero_of_one_le_re`), the value `riemannZeta 0 = -1/2`,
and - decisive for us - the Loeffler-Tao fractional-part machinery
(`Mathlib.NumberTheory.Harmonic.ZetaAsymp`): `termTSum s = 1/(s-1) -
zeta(s)/s` for real `s > 1`, with `termTSum` a sum of NONNEGATIVE
elementary integrals, continuous on `[1, inf)` with `termTSum 1 = 1 - gamma`.
The identity extends to `0 < s < 1` - where it reads
`zeta(s) = s/(s-1) - s * termTSum s <= s/(s-1) < 0` - by analytic
continuation: extend `termTSum` to complex `s` with `re s > 0` (the term
series converges locally uniformly there by an M-test against
`(1/2) u^{-sigma-1}`), do the Abel-summation computation
`zeta(s) = s/(s-1) - s * termTSum s` for complex `re s > 1` against
mathlib's `zeta_eq_tsum_one_div_nat_cpow`, and conclude by the identity
theorem on the punctured half-plane `re s > 0 \ {1}` (both sides analytic
there; no removability needed).  Cost estimate: an afternoon-sized file
(term-analyticity via the closed form + M-test, or a parameter-integral
lemma; the Abel computation ~40 lines; connectedness of the punctured
half-plane the only geometry).  Until then the input stays a named
hypothesis - never an axiom - and everything downstream of it is proved.

## Not yet done

- The discharge of `ZetaNoRealStripZeros` (the plan is above; until then
  the mirror direction carries it as its single named hypothesis).
- T1's effective content (explicit constants from the paper's Definition
  6.1, computed address - the shadow, `Shadow/`); the `Y0` in `t1Soft`
  made explicit.
- T1-L: the archive's even-character statements - the family-level
  machinery is fully lifted (`zeroFree_of_rpow_window`), but the
  non-trivial-character instantiation (`Gchi` at `chi != 1`, the `L'`/`L`
  correction) and the `Schi`-facing statements are not yet ours.  Note
  that for L-functions the mirror direction is NOT available on the cheap:
  real strip zeros (Siegel zeros) genuinely exist as a possibility, so the
  `s0 = -1` disjunct there needs the stronger zero-free input.