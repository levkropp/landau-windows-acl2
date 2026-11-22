# Roadmap

## Phase 0 — Foundations ✅ (this commit)

Statements drafted (`docs/statement.md`), prior art surveyed (`docs/prior-art.md`), README written.

**Success criterion:** a stranger who watched the video can say in one sentence what this repo is about; a number theorist can say in one sentence what's new.

## Phase 1 — The explicit windowed Landau theorem (classical paper)

**Status (2026-11-21): core delivered and compiled; phase in progress.** `classical/paper.tex` is drafted in full — the explicit windowed Landau certificate theorem T1 (Theorem 6.2 there) with every constant rational and listed in its Constant Registry — and the certificate algorithm is specified in `classical/certificates.md`. The first compile pass is done (MiKTeX 25.12; `paper.pdf`, 27 pages, no errors). Pending: the `numerics/` sanity checks, and (optionally, Phase 1.5) the cluster refinement of paper §8.1.

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

**Status (2026-11-22): started, core in place and building clean; T1 statement landed; discharge plan concrete.** The `lean/` lake project is pinned to the archive's toolchain (Lean v4.33.1) and mathlib (rev `0df444a…`) for maximal lift fidelity, and the *entire* abstract windowed-Landau cluster is lifted from the Alpöge archive (14 files, provenance headers, imports rewritten; compiles against vanilla mathlib alone). Our ζ-instantiation `LandauWindows.zeta_landau_windowed` — Rubinstein's windowed lemma for ζ — is **proved** from the lifted core plus two elementary bridges, with the analytic content (Mellin identity, pole structure, growth) packaged as ONE named hypothesis `ZetaPoleData` (hypothesis injection; never an axiom). `lake build` completes with zero errors and zero sorries, and the build-enforced axiom audit (`LandauWindows/Axioms.lean`) shows every theorem depends on exactly the three standard Lean axioms. T1's soft statement (certificate data, (V1)–(V5), (S1), the windowed-violation conclusion) is in `LandauWindows/T1.lean`, and the `ZetaPoleData` discharge plan is now concrete — mathlib at our pin has `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (the `∑ Λ(n)/n^s = −ζ'/ζ` identity), and the ramp-integral brick (`MellinRamp.lean`) is lifted; per-field plan in `lean/README.md`. Pending: the discharge itself, the `s₀ = -1` mirror direction, the explicit constants of T1, the effective shadow.

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

Deliverable: a `docs/` note situating the effective shadow: expected somewhere in RCA₀–PA (the window conversion should be elementary; the transcendence of the zero-isolation is an *input*, which is what keeps this low). This is a genuinely new datapoint for the reverse mathematics of analytic number theory.

**Success criterion:** a precise theorem or a precise plan for one.

## Phase 4 — ACL2 certificate checker

Deliverable: an ACL2 project in `acl2/` verifying the finite core:

- definitions: Λ-sums over bounded ranges as terminating functions on rationals (scaled integers), interval comparisons, the certificate data structures;
- theorem: for all valid certificate data, the check at the computed address succeeds — an ACL2-shaped universally-quantified statement about terminating functions;
- if limits sneak back in anywhere, ACL2(r) (nonstandard analysis extension) is the fallback home, but the target is vanilla ACL2.

**Success criterion:** `acl2` certifies the checker with no `skip-proof`s and no nonstandard extensions, and the checker, run on a synthetic certificate, terminates.

## Non-goals

- Proving the Riemann Hypothesis (in any system).
- Formalizing theta lifts, Bost's slope inequality, VWin, or any part of the Alpöge "step three" machine.
- Arithmetizing anything with automorphic content — that is a research program (Macintyre/McLarty-style), not a port; the archive's machine verification (Nov 21, 2026) does not change this, since the obstacle is proof-theoretic strength, not trust.
- Competitive numerical constants (an explicit-verification-grade version is a natural follow-up with the community that does that for a living).
