# Part Seven: complex phases and oscillating samples

This episode builds the complex-valued computation left open in Part Six:
exact rational pairs, length-preserving rotations, an approximate phase,
an oscillating weighted sample, and a finite list of those samples. The
real interpretation and the remaining integral and pole arguments stay
explicit throughout.

## Actual project constructions

Thirty-six definitions are shown completely before compact use. Related
short definitions share a readable source card; the sample checker spans
two numbered pages.

| Project source | Functions shown |
| --- | --- |
| [complex-bounds.lisp](../acl2/complex-bounds.lisp) | `lw-complexp`, `lw-complex-add`, `lw-complex-sub`, `lw-complex-scale`, `lw-complex-mul`, `lw-complex-diskp`, `lw-complex-power` |
| [mellin-sums.lisp](../acl2/mellin-sums.lisp) | `lw-diskp` |
| [phase-bounds.lisp](../acl2/phase-bounds.lisp) | `lw-phase-denominator`, `lw-phase-rotation`, `lw-phase-grid`, `lw-phase-steps`, `lw-phase-value` |
| [log-signal.lisp](../acl2/log-signal.lisp) | `lw-log-signal-cap`, `lw-log-signal-lipschitz`, `lw-log-signal-budget`, `lw-log-signal-delta`, `lw-log-signal-point`, `lw-log-signal-margin`, `lw-log-signal-base`, `lw-log-signal-bounds` |
| [mellin-integrand.lisp](../acl2/mellin-integrand.lisp) | `lw-mellin-signal-cap`, `lw-mellin-kernel-cap`, `lw-mellin-component-error`, `lw-mellin-signal-error`, `lw-mellin-kernel-error`, `lw-mellin-phase-error`, `lw-mellin-signal`, `lw-mellin-weight`, `lw-mellin-phase`, `lw-mellin-sample`, `lw-mellin-sample-check` |
| [mellin-quadrature.lisp](../acl2/mellin-quadrature.lisp) | `lw-mellin-cellsp`, `lw-mellin-sum-raw`, `lw-mellin-sum-error`, `lw-mellin-sum` |

Source cards read isolated certified snapshots. The preparation script does
not change the project books.

## Rational phase and its interpretation

A complex point is a dotted pair `(real . imaginary)`. An interval or cell
can use the same pair representation with a different meaning. Complex
multiplication is `(x,y)*(u,v)=(xu-yv,xv+yu)`. The disk predicate uses the
exact squared comparison `x*x+y*y <= radius*radius` with a nonnegative
radius; two coordinate bounds alone do not establish a disk bound.

The rational rotation is
`R(t)=((4-t*t)/(4+t*t), 4*t/(4+t*t))`. Its denominator is positive and
`(4-t*t)^2+(4*t)^2=(4+t*t)^2`, so its length is exactly one. It approximates
the angle: `R(1)` is not `exp(i)`. With positive natural `N`, the phase grid
is `P_N(t)=R(t/N)^N`.

[PhaseBounds.lean](../lean/LandauWindows/Soft/PhaseBounds.lean) proves the
real bridge. In particular, `phaseGrid_exp_bound` gives distance at most
**`2*t*t/N`**, provided `abs(t) <= N` and `N > 0`. The computed step count
meets both the domain restriction and the requested positive rational
error. Generic arithmetic bounds compare rational phase grids; the bridge
identifies their target with `exp(i*t)` and proves its unit norm. The
[NIST Euler identity](https://dlmf.nist.gov/4.14.E3) records the usual
`exp(i*t)=cos(t)+i*sin(t)` interpretation.

At log address `u`, the Mellin phase is `exp(-i*H*u)`, with rational height
`H` of either sign. The scalar signal is `g(u)=Gz(exp(u))`. Since `exp(u)`
need not be rational, the actual log-signal computation chooses a nearby
rational input and pays a proved transport margin. It does not simply
round the input and keep the old tolerance. See
[LogSignal.lean](../lean/LandauWindows/Soft/LogSignal.lean).

## Samples and error budgets

Coarse caps `M` for the computed signal magnitude and `K` for both kernel
weights are chosen before final component tolerances. The cap `K` is not
the kernel order (`index` in the code). This order avoids a circular
precision choice.

Changing one factor at a time gives the sample-distance allowance
`K*delta_signal + M*delta_weight + M*K*delta_phase`. The component tolerance
is `error/[3*(1+factor)]`; the signal tolerance is additionally capped at
one. Scalar approximations are the **lower endpoints**, so the **full
interval widths**, rather than half-widths, bound their errors.

The sample checker checks the rational premises: caps, interval widths,
nonnegative weights and the amplified error budget. The generic phase
theorem supplies phase accuracy; no trigonometric oracle is evaluated by
the checker. The stated sample domain requires nonnegative rational
address, decay rate and cell weight; rational height; natural kernel
order; and positive rational error.
[MellinIntegrand.lean](../lean/LandauWindows/Soft/MellinIntegrand.lean),
including `real_product_phase_error` and `mellinSample_sound`, proves the
corresponding interpretation with its hypotheses attached.

A cell stores `(address . weight)`. `lw-mellin-cellsp` checks finite list
data, not interval coverage. The sum traverses that list and adds the
actual computed samples. It assigns each weighted sample `error/(N+1)`;
the complex triangle inequality then controls the finite sum's evaluation
error. [MellinQuadrature.lean](../lean/LandauWindows/Soft/MellinQuadrature.lean),
`mellinSum_sound`, connects that computation to the intended finite sum.
Mesh error and the omitted infinite tail remain separate obligations.

The one-sided estimate retains the extra plain real reading:
`abs(oscillating sum) + plain reading <= positive-contribution budget`.
The animation does not discard that term.

## Checked examples and certification

| Quantity | Exact result |
| --- | --- |
| `(3/5,4/5)` multiplied by `i` | `(-4/5,3/5)` |
| `R(1)`, `R(-1)`, `R(1/2)` | `(3/5,4/5)`, `(3/5,-4/5)`, `(15/17,8/17)` |
| `P_2(1)` | `(161/289,240/289)` |
| Phase step count for `t=1`, error `1/4` | `9`, with bound `2/9 < 1/4` |
| Illustrative `M=2`, `K=3`, error `1/10` | Component tolerances `1/120`, `1/90`, `1/210`; amplified sum less than `1/10` |
| Illustrative signal `-2`, weight `1/2`, phase `(3/5,-4/5)` | Sample `(-3/5,4/5)` |
| Illustrative contributions `(-3/5,4/5)+(1/5,-1/5)` | `(-2/5,3/5)` |
| Two cells, sum error `1/10` | Point allowance `1/30`; total allowance `1/15 < 1/10` |

The illustrative caps and sample components are not asserted outputs at a
particular address. Neither are the illustrative vector-sum contributions
asserted outputs at the earlier example cells. Plotting uses approximate
screen coordinates; certificate endpoints use exact rationals.

[teaching-part07.lisp](teaching-part07.lisp) exports ten additional teaching
theorems: `video-quarter-turn`, `video-rotation-polynomial`,
`video-rotation-examples`, `video-phase-grid-example`, `video-phase-order`,
`video-component-budget-example`, `video-component-budget-general`,
`video-negative-sample`, `video-vector-sum`, and `video-cell-allocation`.
Local proof-support lemmas are separate from those ten results.

[prepare_part_seven.py](prepare_part_seven.py) stages all 25 project
dependency books through `mellin-quadrature` and certifies them and the
teaching book with vanilla ACL2 8.5: **26 certificates**. Hashes, snapshots
and the certification log are under ignored `.tools/acl2-part07/`. The
three Lean files are frozen interpretation sources; this preparation step
does not recertify Lean. No skipped proofs, trust tags, new axioms or
ACL2(r) are added. Teaching results remain separate from the project's
exported theorem count.

An evaluated finite sum is not yet an improper moment or a pole
contradiction. Final composition, general-zero applicability and the
intended Peano Arithmetic interpretation retain their own proof
obligations. This episode does not declare the full reduction complete.
