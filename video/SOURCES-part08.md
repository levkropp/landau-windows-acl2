# Part Eight: poles, zero covers and the conditional contradiction

This episode follows the finite chain from an isolated pole to a
conditional window witness. Its small points, boxes and two-pole function
are explicitly illustrative. They are not certified zeta-zero data. The
full analytic model and complete-cover obligations remain visible in the
film; the conditional theorem is not substituted for the full reduction.

## Source cards

Thirty-two definitions and one complete teaching-theorem form are shown.
Longer source is split across numbered pages; forms come from isolated
certified snapshots.

| Project source | Definitions shown |
| --- | --- |
| [complex-geometric.lisp](../acl2/complex-geometric.lisp) | `lw-complex-conjugate`, `lw-complex-norm-square`, `lw-complex-reciprocal` |
| [pole-lower.lisp](../acl2/pole-lower.lisp) | `lw-pole-coefficient` |
| [pole-geometry.lisp](../acl2/pole-geometry.lisp) | `lw-plane-pointp`, `lw-distance-squared`, `lw-tie-numerator`, `lw-tie-denominator`, `lw-tie-height`, `lw-avoid-height-interval`, `lw-chosen-height`, `lw-nearest-point`, `lw-other-points`, `lw-isolating-radius-squared` |
| [box-circles.lisp](../acl2/box-circles.lisp) | `lw-boxp`, `lw-box-contains`, `lw-square-interval`, `lw-distance-box`, `lw-boxes-outside-circle`, `lw-circle-check` |
| [zeta-pole-lower.lisp](../acl2/zeta-pole-lower.lisp) | `lw-zeta-residue-denominator`, `lw-zeta-pole-residue` |
| [pole-radius-dominance.lisp](../acl2/pole-radius-dominance.lisp) | `lw-pole-regular-coefficient` |
| [cauchy-extraction.lisp](../acl2/cauchy-extraction.lisp) | `lw-cauchy-boundary-check` |
| [mellin-pole-bridge.lisp](../acl2/mellin-pole-bridge.lisp) | `lw-zeta-model-coefficient`, `lw-zeta-model-polynomial`, `lw-mellin-model-boundary-check` |
| [mellin-real-anchor.lisp](../acl2/mellin-real-anchor.lisp) | `lw-mellin-real-anchor-bound` |
| [mellin-window-budget.lisp](../acl2/mellin-window-budget.lisp) | `lw-mellin-window-decay-index`, `lw-mellin-model-error-precision` |
| [teaching-part08.lisp](teaching-part08.lisp) | `video-eight-geometric-prefix`, `video-eight-toy-coefficient`; theorem `video-eight-separated-bounds` |

Imported helper calls remain connected to their certified dependency
books. The film does not attempt to teach the entire dependency tree.

## Pole coefficients and finite examples

The prefix function sums powers zero through `count-1`, returning zero for
count zero. At `x=1/2`, three terms total `7/4`; adding the exact geometric
remainder `1/4` gives `1/(1-x)=2`. The finite identity requires no infinite
sum. The analytic limit uses `abs(x)<1`.

For `c/(a-z)` with nonzero offset `a`, the coefficient of `z^j` is
`c/a^(j+1)`. Its analytic expansion is valid for `abs(z)<abs(a)`.
The simple teaching model is `1/(2-z)-3/(3-z)`: coefficient zero is `-1/2`,
while coefficient five is `179/15552`. Multiplication by `2^6` gives
`179/243 > 1/2`; the competing relative magnitude is
`3*(2/3)^6 = 64/243 < 1/2`. These are rational model calculations, not
values of the actual Mellin transform.

The regular-part estimate `abs(h_j)<=B/R^j` requires the analytic and
boundary hypotheses of Cauchy's coefficient estimate. The unit-variable
polynomial coefficient is rescaled by `R^(-j)` for the physical variable
`z=R*w`. The finite development uses a polynomial representation,
prescribed rational boundary orbit, computed sample count and proved
extraction allowance. Finite samples alone do not bound an arbitrary
analytic function between samples. Classical context is provided by
[NIST's Cauchy integral formula](https://dlmf.nist.gov/1.9) and
[Taylor and Laurent expansions](https://dlmf.nist.gov/1.10).

The zeta pole coefficient convention is `-m/[rho*(rho-1)]`, with positive
natural multiplicity and `rho` different from zero and one. The input
`rho=1/2+i` yields `4/5` for multiplicity one and `8/5` for multiplicity two.
It is explicitly **not asserted to be a zeta zero**. Multiplicity at a
single location is different from several distinct points in one box.

## Geometry and its actual-zero hypotheses

The rational point example uses `(1,1)`, `(1,-1)` and `(0,0)`, all left of
the line `sigma=2`. Candidate tie heights are `-1,0,1`. Avoiding that list
in `(-1,1)` leaves `[1/2,3/4]`, whose midpoint is `5/8`. Squared distances
there are `73/64`, `233/64` and `281/64`. With cap four, the isolating
squared radius is `153/64`. The construction needs a finite nonempty
point list, the strict left-of-center condition and a cap above the
selected squared distance. Repeated equal copies are removed together.

The **separate** box example uses center `(2,1)`, selected box
`(59/100 61/100 99/100 101/100)` and its reflected competitor. Exact
squared-distance enclosures are `[19321/10000,9941/5000]` and
`[29461/5000,30141/5000]`. Thus selected distances are below two and other
distances above five, so squared radius three passes. Those displayed
summaries are conservative; the checker uses the exact intervals.
The ACL2 circle-check parameter named `radius` stores a **squared radius**.
Square roots appear only in drawing coordinates.

[CertificateGeometry.lean](../lean/LandauWindows/Soft/CertificateGeometry.lean),
`circleCheck_isolates`, transfers checked boxes to actual complex points
under a complete-cover hypothesis and uniqueness of the selected zero
location inside its box. That zero can have higher multiplicity. Checking
supplied boxes does not generate a complete zero cover or resolve a
cluster containing several distinct zeros.

## Model comparison and conditional conclusion

The model polynomial is constructed from the selected pole, a finite
other-pole family and regular coefficients. The boundary checker compares
it with the polynomial from the actual improper Mellin evaluator; it does
not assume coefficient agreement. Its soundness is conditional on the
checks and domain hypotheses. The current numerical improper-polynomial
construction uses `sigma-innerRadius>2`; increasing a cutoff does not
prove meromorphic continuation beyond that domain.

The extra height-zero real reading remains in the one-sided inequality.
A separate model bounds that anchor and controls its possible negative
contribution. Geometric index requirements and comparison errors then
feed the strict scalar contradiction. The teaching separated-bounds
theorem is only its elementary ordered-arithmetic illustration.

The project theorem `lw-mellin-computed-budget-window-witness` in
[mellin-window-budget.lisp](../acl2/mellin-window-budget.lisp) returns the
actual finite search result and a rational address `x`, with `Y<=x`,
`x*x<=Y*Y*Y`, and a strictly positive lower signal endpoint, **provided the
effective data check passes**. The film summarizes this implication and
does not introduce a new implementation of the full checker.

Analytic model construction, complete covers of general zeros, uniform
compatible caps as precision varies, and the full encoded theorem with
its intended Peano Arithmetic interpretation remain distinct obligations.
See the current [proof ledger](../docs/reduction-status.md).

## Certification

[teaching-part08.lisp](teaching-part08.lisp) exports twelve teaching
theorems: `video-eight-geometric-example`, `video-eight-complex-reciprocal`,
`video-eight-pole-coefficients`, `video-eight-tie-heights`,
`video-eight-avoiding-heights`, `video-eight-nearest-point`,
`video-eight-isolation`, `video-eight-box-distances`, `video-eight-box-circle`,
`video-eight-residue-example`, `video-eight-relative-dominance`, and
`video-eight-separated-bounds`.

[prepare_part_eight.py](prepare_part_eight.py) certifies 93 isolated project
dependency books through `box-circles` and `mellin-window-budget`, plus the
teaching book: **94 certificates**, using vanilla ACL2 8.5. Snapshots,
fingerprints and the log live under ignored `.tools/acl2-part08/`. The Lean
geometry source is frozen for reference, not recertified by this script.
No skipped proofs, trust tags, new axioms or ACL2(r) are added. Teaching
theorems remain separate from the project's exported theorem count.
