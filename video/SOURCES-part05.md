# Part Five: the windowed bridge and its arithmetic illustrations

The film explains the ceiling direction of the repository's **classical**
windowed Landau theorem. For fixed `0 < theta < 1` and `C > 0`, ceilings
`Gz(x) <= C*x^theta` throughout arbitrarily large windows `[Y,Y^(3/2)]`
exclude zeta zeros with real part strictly greater than `theta`.
The constant and exponent are fixed before choosing windows. The ceiling
is a hypothesis; the episode does not construct the ceiling needed by RH.

## Classical statement and proof sources

- [ZetaPoleData.lean](../lean/LandauWindows/Soft/ZetaPoleData.lean),
  `zeta_landau_windowed_unconditional`: the actual theorem statement
  displayed in the film. Its analytic bundle has been discharged; the
  window-ceiling hypothesis remains part of its statement.
- [ZetaWindowed.lean](../lean/LandauWindows/Soft/ZetaWindowed.lean):
  `gz(u)=Gz(exp(u))`, the strip zero set, and the ceiling-to-window bridge.
- [PoleData.lean](../lean/LandauWindows/Soft/PoleData.lean): transform,
  growth, isolation, and local pole data used by the abstract theorem.
- [landauWindow.lean](../lean/LandauWindows/Soft/landauWindow.lean):
  the full classical argument, including its geometry and coefficient
  estimates. The animation is an explanation of its structure, not a new
  proof of all its analytic lemmas.
- [The classical paper](../classical/paper.tex), introduction and the
  transform, kernel and one-sided-bound sections. The current paper's
  effective certificate theorem has explicit applicability conditions;
  it must not be confused with an unconditional effective ACL2 result.

The [NIST zeta definition](https://dlmf.nist.gov/25.2) supplies the series
domain and analytic-continuation terminology. Its [zero summary](https://dlmf.nist.gov/25.10)
and [reflection formulas](https://dlmf.nist.gov/25.4) describe the strip,
critical line and symmetries. Reflection at the same height combines the
functional equation with conjugation.

## Assets and visual conventions

`ZeroMap`, its sample zero ordinates, `CeilingPlot`, and `WavePanel` come
from the original video repository at the revision pinned in
[reference.json](reference.json). The local adapter supplies Windows fonts.
Part Five adds its own teaching scenes around these credited assets.

Purple off-line zero dots are hypothetical. Ceiling/wave pictures and the
pole geometry are labelled schematic. They are not computations of the
actual zeta signal or certificates for any off-line zero. Kernel curves
are each divided by their own peak; their absolute masses cannot be
compared from that picture. Outside tails and competing poles remain
explicit proof obligations. The film uses `t` for a zero's height, keeping
it distinct from the Euler constant in Part Four.

The local pole expansion is `Phi(s)=c/(s-rho)+h(s)`, with `c != 0` and
`h` analytic near `rho`. The schematic coefficient scale `d^(-k)` absorbs
constant factors; deriving compatible bounds for the actual coefficients
requires the complete geometry and remainder estimates. Multiple zeros
and clusters cannot be omitted.

## Checked arithmetic

[prepare_part_five.py](prepare_part_five.py) stages the four dependency
books of `landau-bounds.lisp` (including that book), plus
[teaching-part05.lisp](teaching-part05.lisp), under ignored
`video/.tools/acl2-part05/`. It certifies all five books using vanilla ACL2
8.5, without altering the project proof tree. Source cards read the same
snapshots. Changed source fingerprints trigger recertification.

The six additional exported teaching theorems are:

| Theorem | Scope |
| --- | --- |
| `video-positive-part-identity` | `abs(x)+x=2*max(x,0)` for rational inputs. |
| `video-three-one-sided` | Three rational values with unit weights and fixed real phases `(+1,-1,+1)` satisfy the combined-reading bound. |
| `video-one-sided-examples` | The examples `(-3,2,-1)` and `(-10,2,-1)` both give combined reading 4. |
| `video-geometric-demo` | The project index is 17 for base `3/2`, target 8, and every natural order at least 17 reaches 8. |
| `video-midpoint-gap` | For rational `1/2 < beta < 1`, epsilon half the gap gives `1/2 < 1/2+epsilon < beta < 1`. |
| `video-window-endpoints` | The endpoint examples satisfy `8^2=4^3`, `64^2=16^3`, and `512^2=64^3`. |

The general three-value inequality is a restricted real example. The
project's actual complex, nonnegative-weight version is proved in
[mellin-sums.lisp](../acl2/mellin-sums.lisp), including
`lw-mellin-one-sided-bound`. The magnitude **plus the plain real reading**
is controlled. Removing that real reading without an additional bound
would be invalid; the film explicitly retains it.

`lw-geometric-index` is displayed from the actual project source.
Its sufficient bound follows from Bernoulli's inequality for repeated
multiplication. The index 17 is conservative: the sixth power of `3/2`
already exceeds 8. The theorem does not manufacture the analytic inputs
needed by the full Landau contradiction.

The fingerprint, certificate list and log are under
`.tools/acl2-part05/certified-sources.json` and `certify.log`. Five Lean
files are also frozen as source snapshots; the preparation script does
not recertify Lean. No skipped proofs, new axioms, trust tags or ACL2(r)
are introduced by the teaching book. Teaching results are separate from
the project's exported theorem count.

## Scope

The effective full reduction, general zero applicability, and its intended
Peano Arithmetic interpretation have their own outstanding obligations in
the proof ledger. This film does not claim they are complete. Nor does it
claim this component is the only possible arithmetic reduction of an RH
argument, or rule out a full proof of RH in Peano Arithmetic.
