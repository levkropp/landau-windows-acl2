# classical/ — the explicit windowed Landau theorem (Phase 1)

This folder holds the classical paper: **Landau's ceiling step on windows, with explicit constants**, plus the certificate algorithm.

Contents:

- `paper.tex` — the paper (drafted 2026-11-21): the effective windowed Landau certificate theorem T1 (Theorem 6.2), matching the target statements in `docs/statement.md` §3. The absolute constants are listed in the Constant Registry (§9); derived quantities involve computable real expressions that still need certified rational enclosures in the implementation.
- `paper.pdf` — the compiled paper: 28 pages, built with MiKTeX 25.12 (`pdflatex` in this folder). The cluster discussion now distinguishes the draft's fixed-slab restriction from the remaining effective zero-cover obligations.
- `certificates.md` — the certificate algorithm: input/output formats, pseudocode, termination and complexity; the transcript format is the interface for the eventual ACL2 checker (T3).
- `numerics/` — planned: sanity-check computations of the constants on synthetic data (see `certificates.md` §6).

The paper records the original single-zero construction. The certified
ACL2 theorem uses arbitrary-precision probes in a compact disk and
constructs the compatible contours for the returned-address certificate.
Its rational mesh, signal enclosures and window thresholds are recorded
with the classical comparison.
[ACL2 interpretation](../docs/acl2-interpretation.md)

## Outline of the argument

1. **Setup.** θ ∈ [1/2, 1); isolation rectangle R (rational vertices) for the alleged zero ρ with Re ρ = β > θ; ceiling constants (C, Y); window [Y, Y^{3/2}].
2. **The kernel identity.** High derivatives of the Mellin transform of the ceiling-violating signal, evaluated along a real vertical slice — the Pólya/Ingham method (cf. Rubinstein, Part II §1, "an estimate of high derivatives of F, which see only one interval at a time").
3. **Effectivization.** Replace every implicit constant in the one-page proof with a computable numeral; replace every existence with a bounded search. The technical risk is the k-th-derivative bound: k must be explicit in (θ, R, C, Y) for the search to terminate.
4. **The certificate.** Inputs → (address x ∈ [Y, Y^{3/2}], margin). Verification at x: Λ-sum to an explicit bound vs. rational interval comparisons. Finite arithmetic, no analysis.
5. **L-function variant** (stretch): same for Dirichlet L-functions, matching the archive's `Gchi`-based statements (`docs/statement.md` §4).

## What this folder is *not*

Not dependent on the fate of the Alpöge claim — which was, for the record, independently machine-verified the day after its announcement (see the README honesty box) — since the windowed lemma's statement and its one-page non-effective proof exist in the classical literature as of 2026-11-21, and our contribution is explicitness + computability.
