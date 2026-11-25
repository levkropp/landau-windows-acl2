# Lean formalization

The soft layer proves correctness in ordinary mathlib mathematics. The
arithmetic shadow supplies explicit algorithms and proofs suitable for the
ACL2 target. The full effective Landau reduction is still in progress.

## Build

```
cd lean
lake update
lake exe cache get
lake build
```

Pins: Lean `v4.33.1`; mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, matching the source archive.
Fetch dependencies and cached oleans once; the initial cache is several GB.

## Proof inventory

| Module | Result | Status |
|---|---|---|
| `Statement.lean` | `Sz`, `Gz`, `ZetaLandau`, `ZetaLandauEps` | Archive statements, with provenance |
| `Soft/Landau*.lean` and supporting modules | Abstract windowed Landau | Lifted and compiled |
| `Soft/CharFamily.lean` and analytic chain | Character-family `PoleData` construction | Lifted and compiled |
| `Soft/ZeroFreeOfRpowWindow.lean` | Family-level windowed zero-freeness | Lifted and compiled |
| `Soft/ZetaPoleData.lean` | `zetaPoleData`; unconditional windowed ceiling theorem for zeta | Proved |
| `Soft/ZetaReal.lean` | Fractional-part integral continuation; zeta negative on `(0,1)` | Proved |
| `Soft/ZetaLandau.lean` | Floor direction; both signs of the archive's Landau statements | Proved, all analytic inputs discharged |
| `Soft/CertificateGeometry.lean` | Real meaning of squared-distance circle checks and rationally rounded window meshes | Proved; complete zero covers remain explicit inputs |
| `Soft/LogBounds.lean`, `Soft/EulerBounds.lean` | Real meaning of the ACL2 rational logarithm and Euler-constant evaluators | Proved |
| `Soft/RpowBounds.lean` | Real meaning of the ACL2 root-bisection evaluator for rational powers | Proved |
| `Soft/PrimePowers.lean` | Standard primality/prime-power interpretation of the bounded searches; von Mangoldt enclosure soundness | Proved |
| `Soft/SignalBounds.lean`, `Soft/SignalSearch.lean` | Actual signal enclosure and accepted-violation soundness; peak-based search bridge; meaning of the rational ceiling derived from search failure | Proved; effective pole comparison remains open |
| `Soft/SignalWindow.lean` | Continuity on positive intervals and extension of the rational ceiling to the original closed real window | Proved, including the irrational upper endpoint |
| `Soft/ExpBounds.lean`, `Soft/KernelBounds.lean` | Actual exponential interpretation of computed Taylor/reciprocal bands and enclosure of the constructed Mellin kernel weights | Proved |
| `Soft/PhaseBounds.lean` | Rational Cayley phase samples have exact unit norm and approximate `exp(i*t)` within the computed error budget | Proved |
| `Soft/LogSignal.lean` | Explicit `Gz` Lipschitz bound and actual enclosure of `Gz(exp u)` by the computed rational log-variable evaluator | Proved, including `u=0` |
| `Soft/SpatialBounds.lean` | Computed uniform exponential and `Gz(exp u)` Lipschitz constants, precision-free enclosure transport and a positive rational mesh modulus on the entire real log interval | Proved |
| `Soft/KernelSpatial.lean`, `Soft/MellinSpatial.lean` | The same computed kernel and product constants bound the actual Mellin integrand on the entire real log interval | Proved; no assumed analytic slope bound |
| `Soft/MellinIntegrand.lean`, `Soft/MellinQuadrature.lean` | Rational constructor checks imply accuracy for the actual weighted Mellin integrand and exact finite sum | Proved; ACL2 proves all constructor checks |
| `Soft/MellinPartitions.lean` | Computed dyadic depth and point precision give the requested error for the actual bounded integral | Proved under the rational leaf checks universally verified in ACL2 |
| `Soft/MellinTail.lean` | Global quadratic `Gz` growth, an inverse-square kernel majorant, improper-tail integrability/error, and the same computed cutoff budget | Proved |
| `Soft/MellinIntegral.lean` | The assembled evaluator approximates the full improper transform within its requested error; semantic Cauchy bound across cutoffs | Proved under the rational constructor checks universally verified in ACL2 |
| `Soft/WindowIndex.lean` | Checked rational derivative-index band implies the true logarithmic kernel bounds and interior containment | Proved |
| `T1.lean` | Certificate data, validity conditions, `t1Soft` | Existence theorem proved; threshold not made effective |
| `Shadow/Interval.lean` | Scaled-integer interval propagation; bounded-search soundness and completeness with a margin | Proved, choice-free |
| `Shadow/Grid.lean` | Computed mesh witness; quantitative grid-search completeness | Proved, choice-free |

## What is lifted

The archive's entire windowed-Landau cluster is lifted: the 14-file abstract
core, character-family construction and analytic chain, full
`WindowHypOfRpow` / `WindowHypUOfWindowHyp`, `lemmaL`, and
`ZeroFreeOfRpowWindow`. Each lifted file identifies its source path and
records import-only changes. `PoleDataConstruction.lean` is the archive's
`poleData.lean`, renamed to avoid a Windows case-insensitive collision.

The archive's `Ch*`, `SplitInertia`, and `RunBase...` arithmetic files
construct the upstream ceiling. They are outside this project's step-2 scope.
Statement hygiene: compare a lifted declaration against the source named in
its provenance header before changing or freezing its meaning.

## How the zeta proofs close

**The analytic bundle.** The lifted construction
`Deduction.poleData F` produces `PoleData` for an admissible character family.
`ZetaPoleData.lean` instantiates it at the conductor-1 trivial family and
identifies the family statistic and zero set with `Gz` and the zeta strip
zeros. This proves `zetaPoleData`, then
`zeta_landau_windowed_unconditional`. The soft certificate theorem `t1Soft`
is a logical consequence: a zero to the right forces violations in every
sufficiently large window.

**Real-strip nonvanishing.** Write
`I(s) = integral_1^infinity fract(t) * t^(-s-1) dt`.
The bounded fractional-part tail is locally integrable and zero near 0.
Mathlib's Mellin differentiability theorem makes `I` analytic for `Re s > 0`.
Abel summation gives the identity for `Re s > 1`. Removing the pole first,
the identity theorem on the connected right half-plane proves

```
riemannZeta₁(s) = s - s (s-1) I(s).
```

Away from 1 this gives `zeta(s) = s/(s-1) - s I(s)`. For real `0 < x < 1`,
`I(x)` is nonnegative, so `zeta(x) <= x/(x-1) < 0`. Thus
`riemannZeta_ne_zero_of_mem_Ioo` discharges `ZetaNoRealStripZeros` as
`zetaNoRealStripZeros`.

**The mirror direction.** A floor on `Gz` is a ceiling on `-Gz`.
`poleData_neg` transfers the analytic bundle when the zero set has no real
points. Nonvanishing on the real strip supplies that condition. Consequently
`zeta_landau_windowed_floor`, `zeta_landau`, and `zeta_landau_eps` no longer
take an analytic-input argument. Functional-equation reflection is not the
argument for this same-half-plane floor statement.

## Arithmetic shadow and audit

The shadow imports Lean core integer/list arithmetic and tactics, without
mathlib. Intervals carry **integer numerators at a common positive
denominator**, kept explicit by the caller. Their statement path has no
real numbers, normalized rational quotients, or choice-selected witnesses.
Interval scaling here is by an integer; general rational rescaling and
transcendental bounds still need implementation.

`firstAbove` computes a witness from a finite list. Its theorems prove both
soundness and success when an enclosure is narrower than the available
margin. `gridIndex` computes a nearby mesh index by integer division.
`grid_search_complete` transports a peak across a bounded mesh and proves
that the interval search succeeds. These are general arithmetic lemmas,
not yet a theorem about zeta.

- `Axioms.lean`: 64 soft theorems, each using exactly
  `[propext, Classical.choice, Quot.sound]`. A build-time guard rejects
  any additional axiom, including `sorryAx`.
- `Shadow/Axioms.lean`: 13 shadow theorems using only `[propext]` or
  `[propext, Quot.sound]`. A build-time guard rejects any other axiom,
  including `Classical.choice` and `sorryAx`.

The corresponding ACL2 books also prove finite interval and mesh-search
results; see [certification instructions](../acl2/README.md). This is progress
toward the arithmetic interpretation, not a completed PA-strength proof of
the analytic Landau theorem.

## Remaining obligations

1. Connect the evaluated Mellin coefficients to the arithmetic upper bound
   from failed search. Bounded and improper quadrature soundness, including
   computed depths/cutoffs and proved analytic tails, are established.
   Arithmetic signal/window comparison across cutoffs still requires proof;
   the semantic Cauchy theorem alone does not discharge it.
2. Integrate the eventual derivative-index threshold and checked kernel band
   into the analytic estimates. ACL2 now proves eventual admission with an
   explicit power-of-two window threshold. The computed mesh, actual signal
   samples and returned-address certificate are connected;
   `CertificateGeometry.lean` covers the real endpoint tail.
3. The paper's effective pole/Cauchy/kernel bounds and explicit threshold;
   connect them to the ceiling derived from search failure. `t1Soft` alone does not
   supply those constants.
4. Generate/refine complete zero-box covers for clustered zeros. The new
   adaptive finite-point geometry and sound box-circle checker do not yet
   discharge that analytic obligation.
5. Connect the final arithmetic theorem to windowed Landau and record its
   precise interpretation in the intended weak theory.
6. Instantiate the lifted family machinery for nontrivial characters.
   The L-function floor direction must account for possible real strip zeros.

See the [proof-obligation ledger](../docs/reduction-status.md),
[arithmetic contract](../docs/arithmetic-contract.md),
[exact statement](../docs/statement.md), and [roadmap](../docs/roadmap.md).
Zero-isolation and other external analytic inputs must remain named
hypotheses until proved; they must never be introduced as axioms.
