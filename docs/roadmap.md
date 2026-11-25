# Roadmap

## Phase 0 — Foundations ✅ (this commit)

Statements drafted (`docs/statement.md`), prior art surveyed (`docs/prior-art.md`), README written.

**Success criterion:** a stranger who watched the video can say in one sentence what this repo is about; a number theorist can say in one sentence what's new.

## Phase 1 — The explicit windowed Landau theorem (classical paper)

**Status (2026-11-22): drafted and compiled; mathematical review in progress.** `classical/paper.tex` gives the explicit single-zero certificate theorem T1 (Theorem 6.2), and `classical/certificates.md` specifies its algorithm. The compiled PDF has 28 pages. The single-zero slab restriction does not establish the full windowed theorem. General cluster handling is required, along with verification of the analytic bounds and their arithmetic implementation. See the [proof-obligation ledger](reduction-status.md).

Deliverable: a paper in `classical/` proving T1 (see `docs/statement.md` §3) with fully computable constants and a certificate algorithm.

Plan of the argument (to be refined):

1. **Setup.** Fix θ, the isolation rectangle R for the alleged zero ρ, ceiling constants (C, Y).
2. **Kernel.** Following the Pólya/Ingham high-derivative method (the "one page" proof of Rubinstein Part II §1): express high derivatives of the Mellin/F-transform along a real point; the window [Y, Y^{3/2}] is what the k-th derivative "sees".
3. **Effectivization.** The classical proof is by contradiction with implicit constants; the work is in *de-implicating*: every big-O gets a numeral; every "there exists x" gets a search procedure with a stopping bound; every appeal to "a zero lies in R" becomes arithmetic with the certificate data. Expect a truncated-kernel variant to be needed so the search terminates.
4. **Certificate algorithm.** Pseudocode: inputs (θ, R, C, Y) → outputs (x, margin) with a finite verification procedure (Λ-sum over primes to an explicit bound, rational interval comparisons).
5. **Numerics.** Sanity-check the constants on realistic data (e.g., first zeros of ζ as fake "rogue zeros" just left of the line — the constants will be terrible, and that's fine; the point is computability, not competitiveness).

**Risks:**
- The high-derivative estimates may effectivize with badly coupled constants (k needed may be enormous relative to the window). Acceptable: the theorem only needs *computability* for the PA-track; competitive constants are a Phase 1.5 concern.
- The window exponent (3/2) is architecture-specific; keep the dependence on the exponent symbolic where possible.

**Success criterion:** a referee (human or AI) can take the paper, implement the certificate algorithm, and — for any input data — either produce the address x or demonstrate the input was not a valid certificate.

## Phase 2 — Lean formalization (two layers)

**Status (2026-11-22): the soft layer's main theorems are PROVED, the archive's statements are proved (both signs), and the entire windowed cluster is lifted.** The `lean/` lake project is pinned to the archive's toolchain (Lean v4.33.1) and mathlib (rev `0df444a.`) for maximal lift fidelity, the entire abstract windowed-Landau cluster is lifted (14 files, provenance headers; vanilla mathlib), the archive's character-family `PoleData` construction is lifted too (11 more files, including the Mellin identities, Mertens bounds, conjugation lemmas) and instantiated at the trivial family, and the archive's tail (`WindowHypOfRpow`/`WindowHypUOfWindowHyp` in full, `lemmaL`, `ZeroFreeOfRpowWindow` - the family-level windowed lemma) is lifted verbatim (the `Ch*`/`SplitInertia` step-3 arithmetic files are deliberately out of scope). Results:

- This **discharges the analytic hypothesis `ZetaPoleData` unconditionally**, giving:
  - `zeta_landau_windowed_unconditional` - **Rubinstein's windowed Landau lemma for zeta, with no hypotheses at all**;
  - `LandauWindows.t1Soft : T1Soft` - **T1 proved in the soft layer** (pure logic from the unconditional lemma: a certified zero with `Re > theta` forces every sufficiently large window to contain a ceiling violation).
- **The mirror (`s0 = -1`) direction is done unconditionally**: `zeta_landau : Formalism.ZetaLandau` (BOTH signs) and `zeta_landau_eps : Formalism.ZetaLandauEps` are proved with no analytic input arguments. A floor on `Gz` is a ceiling on `-Gz`, and `PoleData` passes to the negated statistic (`poleData_neg`) when the zero set has no real points. `Soft/ZetaReal.lean` proves zeta < 0 on (0,1), discharging `ZetaNoRealStripZeros`: the fractional-part integral is analytic for `Re s > 0` by mathlib's Mellin theorem, Abel summation identifies it for `Re s > 1`, and the identity theorem continues the pole-removed identity over the connected right half-plane. The proof is documented in `lean/README.md`.

`lake build` succeeds with zero errors and zero sorries; lifted-file linter warnings remain. The soft audit covers the analytic Landau theorems and the real meanings of the arithmetic evaluators. The separate 13-theorem shadow audit rejects choice and extra axioms. Phase 4 and the [proof ledger](reduction-status.md) track the ACL2 reduction; the [arithmetic contract](arithmetic-contract.md) gives its exact bounds. L-function instantiation remains pending, including real zeros in its floor direction.
Deliverable: a Lean project in `lean/`, building against mathlib, containing:

1. **Soft layer** (correctness first): `ZetaLandau`, the windowed version, and T1 proven in ordinary mathlib style (reals, `Classical.choice` allowed internally).
2. **Effective shadow** (the PA-track artifact): the same statements re-proven over explicit rational interval arithmetic with:
   - no `Classical.choice` (explicit descriptions only);
   - every existential replaced by a computed witness;
   - reals entering only through `x ≤ q` comparisons with explicit rational q and explicit error bounds;
   - no quotients in the statement path (work with explicit representatives).

Discipline borrowed from neighbors: hypothesis-injection (zero-isolation rectangles are hypotheses, never axioms — cf. Hubbard's Dudek formalization) and statement fingerprints (nod to IEANTN's design).

**Success criterion:** `#print axioms` on the shadow's main theorem shows only the three standard axioms or fewer; a mechanizable reading of the shadow as a first-order arithmetic argument is documented (Phase 3's input).

## Phase 3 — Reverse-math placement

Deliverable: a precise arithmetic interpretation of the completed ACL2 theorem, tracking the coding of analytic objects and every external input. Roughly PA strength is the target; termination and a Lean axiom audit alone do not establish that placement. Any comparison with second-order subsystems must also account for the equivalence between the encoded and analytic statements.

**Success criterion:** a precise theorem or a precise plan for one.

## Phase 4 — ACL2 arithmetic Landau theorem

**Certified (2026-11-25).** `lw-euler-window-encoded-zero-reduction`
computes the threshold from the rational zero region and ceiling data.
An encoded zero supplies a rational probe at the computed precision.
On every rational window above threshold, the search returns a rational
address with a positive lower enclosure of the violation.
[Main theorem](../acl2/euler-window-encoded-zero.lisp)

The proof selects compatible contours by scanning real radius bands.
Native real-axis and right-half-plane clearance give a strict radial
gap. A positive real count supplies a small probe which is moved to a
modulated contour using that gap. If the final real circle stays empty,
the original probe supplies the modulated count. The checked circle
pair gives the effective window result.
[Proof ledger](reduction-status.md)

The classical comparison identifies the native Euler limit with
`riemannZeta₁` and interprets the rational signal enclosures. It also
extends the result to real window starts. The natural-induction coding
explains the roughly PA-strength reading.
[Arithmetic and classical interpretation](acl2-interpretation.md)

## Non-goals

- Proving the Riemann Hypothesis (in any system).
- Formalizing theta lifts, Bost's slope inequality, VWin, or any part of the Alpöge "step three" machine.
- Arithmetizing anything with automorphic content — that is a research program (Macintyre/McLarty-style), not a port; the archive's machine verification (Nov 21, 2026) does not change this, since the obstacle is proof-theoretic strength, not trust.
- Competitive numerical constants (an explicit-verification-grade version is a natural follow-up with the community that does that for a living).
