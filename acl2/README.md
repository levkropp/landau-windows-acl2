# acl2/ — the certificate checker (Phase 4)

The end goal: a piece of the RH architecture checked by a system whose logic is approximately Peano Arithmetic.

## Why ACL2 can't take the architecture — and can take this

The full Alpöge-style argument needs: a choice principle (used ~87,000 times in his archive, as `noncomputable`/classical steps), quotient types, real/complex analysis, and objects with no computable witnesses. ACL2's logic is quantifier-free, choice-free, first-order, with total computable functions and induction to about ε₀. Porting the architecture is not on the menu, at any effort level.

The *contrapositive of the ceiling step*, in certificate form, is different. Its check is:

1. a Λ-sum over prime powers up to an explicit bound (finite sum, terminating),
2. compared against explicit rational interval bounds (scaled-integer arithmetic),
3. at one explicit address x, in one explicit window.

That is exactly the shape of theorem ACL2 was built for — universally quantified (free-variable) statements about terminating computable functions.

## What the checker will verify

**Input** (all explicit data):
- ceiling claim: θ (rational slice point), C, window [Y, Y^{3/2}] (rationals);
- zero-isolation certificate: rectangle vertices (rationals), plus the derived Landau constants from Phase 1 (computed upstream or admitted as checked hypotheses);
- the computed address x and margin from the certificate algorithm.

**Theorem** (ACL2 shape): for all valid input data, the violation check at x succeeds — i.e., the finite comparison confirms the ceiling is broken at the named address. Together with the Phase-1/2 guarantee that the constants are sound, this closes the loop: *rogue zero + ceiling cannot both stand*, checked by arithmetic alone.

## Design notes

- Represent rationals as scaled integers; precompute Λ-tables as ACL2 data (like the tiered prime-scan tables in the Dudek formalization's kernel-checked small range).
- If any limit survives Phase 1 effectivization (it shouldn't), the fallback is ACL2(r)'s nonstandard extensions — but the target is vanilla ACL2 with `:doc`-clean books and zero `skip-proof`.
- The checker should also *run*: on a synthetic certificate (e.g., a rectangle around a genuine near-critical-line zero used as a stand-in rogue), termination and success should be executable, not just proven.

## Prior art in ACL2 (there isn't any)

ACL2's number theory library is recognition-level (`primep`, Tonelli–Shanks modular square roots, named crypto-curve primes). No real analysis of ζ, no PNT, nothing analytic — confirmed by the ACL2 workshop's own accounting (44 of the "100 theorems", with the note that ACL2 has "largely focused on proving theorems rather different from these"). If Phase 4 lands, this will be the first genuinely analytic-number-theoretic content in the ACL2 ecosystem.
