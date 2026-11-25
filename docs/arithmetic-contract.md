# The arithmetic witness theorem

The ACL2 books certify the arithmetic windowed Landau ceiling reduction.
They build the signal and the compatible contours, then use an encoded
zero to prove that the window search succeeds above a computed threshold.
The [interpretation](acl2-interpretation.md) gives the complete statement
and classical comparison. The [proof ledger](reduction-status.md) indexes
the finite bounds below.

## Quantitative contract

Take rational grid addresses `a_0 <= ... <= a_N`, with consecutive gaps at
most `d >= 0`. Suppose a rational point `p` lies between the first and last
addresses. Let `P` be a peak value and `L >= 0` a Lipschitz bound. The true
sample values `v_i` satisfy

```
v_i >= P - L * |a_i - p|.
```

Each sample has a rational enclosure `[lo_i, hi_i]` containing `v_i`, of
width at most `e`. If

```
P > threshold + e + L*d,
```

then some lower endpoint exceeds `threshold`. The bounded search returns
such an index, which is in range, and its actual sample value also exceeds
the threshold. `lw-grid-search-complete` proves the existence/success claim;
the search soundness and index theorems are in `interval-search.lisp`.

This accounts for **both losses**: transport from the peak to a grid point,
and finite enclosure error. Merely proving that a search terminates would
not establish that it finds a witness.

The Lean shadow proves the analogous result over integer numerators at a
common positive denominator. `gridIndex` additionally computes the nearby
index on a uniform integer mesh. All 13 audited shadow proofs avoid
`Classical.choice`; the build rejects additional axiom dependencies.

## Applying it to Landau

The intended signal is `H(x) = Gz(x) - (C + r)*x^theta`, for a rational
output margin `r > 0`. The current evaluated search provides:

1. The computed rational grid in `[Y, Y^(3/2)]` and a returned-address check.
2. Verified enclosures of `H` at every grid address, including logs, powers,
   Euler's constant, and the finite prime-power sum.
3. A combined precision budget guaranteeing the requested enclosure width.
4. A fixed search whose failure implies a uniform rational ceiling, with
   constant `C+1`, at every rational point of the window.

ACL2 now supplies arbitrary-width rational enclosures for logarithms,
Euler's constant, and rational powers with exponents in `[0,1]`. Lean proves
that the same computed endpoints contain the corresponding real values.
The bounded prime-power recognizer is now proved sound and complete; its
log/zero evaluator encloses the standard von Mangoldt function.
`lw-signal-bounds` composes the actual smoothed sum and `Gz` and computes
primitive precision from the requested total error. It pads the finite sum
with zero ramp terms up to the integer numerator of `x`. Lean proves that
this sum is exactly `Formalism.Sz` and that a positive computed lower bound
is a violation of the actual ceiling.

`lw-window-signal-search-complete` supplies the general peak-based interface.
`signal-continuity.lisp` now proves the full signal's transport and supplies
the fixed search used by the current reduction: let `B = Y^2`, let `N` be
the integer numerator of `B`, and use

```
L = N + 2*B + 3 + C
error = 1/4
step = 1/(4*(L+1)).
```

If this search fails, every rational `x` in the window has computed signal
upper endpoint at most 1. The encoded `Gz` upper endpoint is then at most
`(C+1)` times the computed power lower endpoint.
`evaluated_ceiling_sound` identifies the corresponding inequality for the
actual statistic. `SignalWindow.lean` proves continuity using a fixed finite
ramp sum on each bounded positive interval, then extends the rational
ceiling to the entire closed real window by density. This includes the
irrational endpoint `Y^(3/2)`.

The next arithmetic component is `mellin-sums.lisp`. For rational samples
`g_i`, nonnegative weights `w_i`, phases `c_i + i*s_i` in the unit disk,
and nonnegative caps `g_i <= b_i`, it proves

```
A  = sum g_i*w_i*(c_i + i*s_i)
A0 = sum g_i*w_i
B  = sum b_i*w_i
|A| + A0 <= 2*B.
```

ACL2 represents the norm inequality by a nonnegative rational disk radius
and a squared-norm comparison. Negative samples can be arbitrarily large
in magnitude: `|g_i| + g_i <= 2*b_i` supplies the required cancellation.
The window rows are constructed from the actual lower `Gz` evaluator at
any positive primitive precision at most 1. Exact one-sided transport
keeps these finer samples below the failed search's ceiling. Tail rows
use the proved `4*x^2` cap from `signal-growth.lisp`. That book also proves
the two-sided growth bound independently of the sum's padding count.

`lw-mellin-bound-with-remainders` propagates an explicit complex coefficient
error `E` and one-sided real coefficient error `E0`, adding `E + E0` to the
radius. The later constructors below instantiate this inequality with actual
Mellin samples and default integral approximations. The pole/Cauchy lower
bound remains a separate obligation.

`exp-bounds.lisp` now constructs arbitrary-width exponential enclosures for
nonnegative rational arguments. It starts beyond `ceil(2*x)`, where each
Taylor term is at most half the previous one. The band is the partial sum
plus twice the next term; ACL2 proves nesting, bounds on every later partial
sum, overlap and Cauchy error. A computed halving depth supplies any requested
positive width. Reciprocal bands enclose `exp(-x)` with no larger width.
Lean's `ExpBounds.lean` identifies these same computed bands with the actual
real exponentials, using convergence of the Taylor series.

`exp-continuity.lisp` compares different arguments through a common later
Taylor sum. The finite slope bound is uniform over all truncation indices:
on `[0,U]` its constant is the rational `K = upperExp(U,1)`. Thus lower-to-upper
transport costs at most `K*abs(u-v)`, with no precision loss. Reciprocal
bands inherit the same bound; individual lower endpoints add their two
requested errors. `SpatialBounds.lean` proves the real exponential bound
on the entire interval using that same computed constant.

`kernel-bounds.lisp` constructs the weight
`h*u^j*exp(-sigma*u)/j!` for rational nonnegative `u`, `sigma`, and `h`.
The Taylor-term recursion supplies `u^j/j!` exactly. The primitive error is
`error/(1 + h*u^j/j!)`, so scaling preserves the requested width. Overlap
and Cauchy bounds are proved in ACL2; Lean proves actual kernel enclosure.
`phase-bounds.lisp` constructs the complex phase by rational rotations:

```
Q(t) = ((4-t^2)/(4+t^2), 4*t/(4+t^2))
P(t,n) = Q(t/n)^n.
```

ACL2 proves that these samples lie in the unit disk. The finite quadratic
remainder for powers gives a block error, then the refinement bound
`|P(t,n) - P(t,n*m)| <= t^2/n`. Comparison through `n*m` gives the Cauchy
bound `t^2/n + t^2/m` for any positive step counts. The computed count is
`1 + max(fuel(abs(t),1), fuel(2*t^2,error))`; it meets both
`abs(t) <= n` and `2*t^2 <= n*error`. Thus precision choices have an
arithmetic Cauchy bound, without assuming an analytic phase as input.
Lean's `PhaseBounds.lean` identifies the same samples with approximations
of `exp(i*t)`, proves exact unit norm, and proves the requested error bound.
For the Mellin phase use the rational argument `t = -height*u`.

`phase-continuity.lisp` proves spatial transport too. A direct rational
identity makes `Q` 1-Lipschitz, and the unit-power difference bound gives
the same constant for `P(_,n)`. Refining two arbitrary counts through their
product then gives
`abs(P(a,n)-P(b,m)) <= abs(a-b) + a^2/n + b^2/m`.
For computed phase values the last two terms are at most half their
respective requested errors. This bound does not assume equal step counts
at neighboring abscissae.

`log-signal.lisp` now evaluates `Gz(exp u)` for every rational `u >= 0`.
It computes a fixed cap `B = 1 + upperExp(u,1)` and transport factor
`L = signalCount(B) + 2*B + 3`. For `b = min(1,error)`, it takes
`delta = b/(4*(1+L))` and the rational sample
`x = lowerExp(u,delta) + delta`. This is strictly greater than 1 even at
`u=0`, stays below `B`, and lies between `exp(u)` and `exp(u)+delta`.
The evaluator encloses `Gz(x)` with error budget `b/2`, then expands both
endpoints by `L*delta <= b/4`. ACL2 proves the resulting width is at most
the requested positive error, and proves overlap and Cauchy bounds across
precision choices.

Lean's `LogSignal.lean` proves actual enclosure of `Gz(exp u)`. Its explicit
`Gz` Lipschitz proof uses a fixed finite ramp sum across integer breakpoints,
the logarithm increment bound, and the Euler-constant bounds.
`ExpBounds.lean` now also proves the computed exponential width in Lean;
the log-variable interpretation assumes no unproved transport or width
premise.

`log-signal-continuity.lisp` uses `B = 2 + K` as a uniform cap for the
computed rational samples on `[0,U]`, and sets
`S = signalCount(B) + 2*B + 3`. Intermediate bounds contain auxiliary
precision terms. ACL2 removes them by contradiction: a positive rational
excess determines an explicit finer precision, and overlap with those
finer enclosures contradicts that excess. The resulting lower-to-upper
transport is at most `S*K*abs(u-v)`. Individual lower endpoints add only
their two requested errors.

The computed positive spacing `delta = error/(4*(1+S*K))` therefore
controls neighboring signal samples: argument distance at most `delta`
and each evaluation error at most `error/4` imply a total difference at
most `error`. Lean proves the corresponding bound for the actual real
function `Gz(exp u)` on the entire interval, with the same `K`, `B`, `S`
and spacing. These bounds now supply the signal component of the composed
Mellin spatial estimate below.

`mellin-integrand.lisp` now composes the three evaluators. Its caps are
independent of the final precision:

```
M = 1 + abs(lowerG(u,1)) + abs(upperG(u,1))
K = 1 + upperKernel(u,sigma,j,h,1)
eg = min(1, error/(3*(1+K)))
ew = error/(3*(1+M))
ep = error/(3*(1+M*K)).
```

The computed sample multiplies the lower signal endpoint, lower kernel
endpoint and rational phase. The product error is at most
`K*eg + M*ew + M*K*ep <= error`. ACL2 proves the caps, budgets, endpoint
checks and Cauchy bound for every valid constructor input. Lean's
`mellinSample_sound` interprets those exact rational checks as accuracy
for the actual integrand; `mellinWeightedValue_eq` identifies the product
with the standard factorial-normalized Laplace integrand. The checks
contain no assumed analytic coefficient estimate or successful search.

`mellin-quadrature.lisp` evaluates a fixed list of nonnegative rational
log-abscissae and weights. With `N` nodes it requests `error/(1+N)` at each
node, so the total evaluation error against the exact weighted sum is at
most `error`. ACL2 proves constructor-check validity, rational output and
Cauchy bounds across precision choices. Lean proves the corresponding
accuracy for the exact finite sum. Grid refinement and the infinite tail
are separate from that fixed-grid result; the following books now supply
the arithmetic refinement bounds.

`kernel-continuity.lisp` supplies uniform spatial bounds for the weights.
Every factorial-normalized polynomial term and its slope are at most
`upperExp(U,1)` on `[0,U]`. Writing `K = upperExp(U,1)`, the kernel cap is
`T = h*K` and the slope is `W = T*(1 + sigma*upperExp(sigma*U,1))`.
The enclosure transport has no added precision loss; lower endpoints add
their two requested errors. `KernelSpatial.lean` proves the same constant
for the actual real kernel, including `j=0` and zero weights.

`mellin-continuity.lisp` composes spatial transport for the existing sample
constructor. Its signal slope is `D = S*K`, and a uniform signal cap is
`M = 2 + abs(lowerG(0,1)) + abs(upperG(0,1)) + D*U`.
The product slope and evaluation factor are

```
L = T*D + M*W + M*T*abs(height)
A = 1 + T + M + M*T.
```

The distance between samples at `u,v` with requested errors `e,f` is at
most `L*abs(u-v) + A*(e+f)`. Thus spacing and point errors bounded by
`error/(4*(1+L+A))` suffice for a total difference at most `error`.
All constants are independent of the final precision and derivative index.
`MellinSpatial.lean` proves that the same `L` bounds the actual real-variable
Mellin integrand throughout `[0,U]`, including the integer breakpoints.

`mellin-partitions.lisp` puts the cell weight outside each unit-weight
sample. It recursively bisects rational intervals, preserving total mass.
Comparing depth `n` with any refinement gives the bound
`length*(L*length/2^n + A*(e+f))`; arbitrary depths are compared by ordering
them. The bounded approximation chooses its depth by halving `L*U^2` to
at most `error/4`, and requests point precision `error/(4*(1+U*A))`.
ACL2 proves both budgets, all leaf constructor checks, rational output,
and a Cauchy bound of `e+f` across these computed depth/precision choices.
This establishes arithmetic convergence under grid refinement.
`MellinPartitions.lean` now identifies the same bounded approximation with
the classical integral, within the requested error. It proves the computed
depth and point-precision budgets too. Its remaining Boolean premise is
exactly the finite leaf-check conjunction proved universally valid by ACL2;
no integral approximation or analytic slope is assumed.

`mellin-tail-bounds.lisp` uses two additional Taylor terms to bound the
positive kernel. For `a > 0`, `a*u >= j+2`, and nonnegative weight `h`,
the computed upper endpoint satisfies

```
u^2 * upperKernel(u,a,j,h,error) <= h*(j+1)*(j+2)/a^(j+2).
```

The starting exponential index already includes the needed Taylor term,
independently of precision. For a uniform grid starting at `R`, with
positive step at most `R`, a reciprocal potential bounds every finite
kernel tail by `2*C/R`, where `C = c*(j+1)*(j+2)/a^(j+2)` includes a
nonnegative mass `c`. The cutoff
`R = 1 + (j+2)/a + ceiling(2*C/error)` meets both the Taylor threshold
and `C/R <= error/2`. All these statements are arithmetic theorems.

`MellinTail.lean` proves the actual growth bound `abs(Gz(x)) <= 4*x^2`
on `x >= 1`. For the Mellin integrand with rational `sigma > 2`, take
`a = sigma-2`, `c = 4`: its norm is at most `C/u^2`, its improper tail
is integrable, and that tail has norm at most `C/R`. No tail estimate is
supplied as a hypothesis.

`mellin-integral.lisp` evaluates bounded quadrature up to that computed
cutoff with requested error `error/2`. ACL2 proves rational output,
universal validity of its constructor checks, and the combined numerical
error budget. `MellinIntegral.lean` identifies it with the full improper
Mellin integral within `error`, and proves a semantic Cauchy bound even
when precision changes the cutoff. The checks contain only cutoff/radius
comparisons and the finite rational leaf checks already proved by ACL2.

`mellin-window.lisp` now applies the one-sided inequality to the actual
dyadic samples. At each log-abscissa it uses the signal constructor's
rational point `x`. If `Y <= x` and `x^2 <= Y^3`, failed search supplies
the cap `(C+1)*lowerRpow(x,p/q)` at the required primitive precision.
Otherwise the proved growth bound supplies `4*x^2`. The row weight and
phase are constructed by the Mellin evaluator. The log-signal transport
margin is nonnegative, so its lower endpoint respects the same cap.

Let `B(error)` be the weighted sum of these computed caps on the default
improper evaluator's dyadic grid, and let `I_h(error)` denote its rational
complex output at height `h`. For rational `Y > 1`, `C >= 0`,
`0 <= p/q <= 1`, `sigma > 2`, rational height, natural derivative index
and positive error, ACL2 proves from failed search:

```
disk(I_h(error), 2*B(error) - Re(I_0(error)) + error/2).
```

The height-zero phase is exactly `(1,0)`, so `I_0` is exactly real.
Its native grid can differ from the height-`h` grid: ACL2 compares the
two dyadic depths using the proved spatial slope, which is smallest at
height zero. Their difference is at most the bounded evaluator's requested
error. This gives the displayed `error/2` term, rather than assuming
coefficient remainders or a shared grid. The radius is an exact rational
disk assertion about computed approximations. The normalization below
refines both native grids to a common grid and bounds its complete window
budget, giving the normalized default coefficient-pair estimate.

`exp-addition.lisp` proves the exponential product laws used in the tail
comparison from finite Taylor convolution. A triangular sum is the Taylor
sum at `a+b`; comparing it with rectangular sums gives both cross bounds
between exponential products and sum-argument enclosures at independent
precisions. In particular,

```
lowerExp(u,e)^2 * lowerExp(a*u,f) <= upperExp((a+2)*u,g).
```

Together with `x <= 2*lowerExp(u,delta)` and the signal transport margin,
this bounds the absolute log-signal lower endpoint by
`17*lowerExp(u,delta)^2`. The actual Mellin sample therefore lies in a disk
of radius `17*upperKernel(u,sigma-2,j,h,shiftedError)`. No exponential
product identity or analytic signal-tail estimate is an input.

The generated uniform cells use the existing `mellin-sum-raw` constructor.
The kernel's telescoping tail bound now proves that their actual complex
sample sum lies in a disk of radius `targetError` after the computed
`tailCutoff(sigma-2,j,17,targetError)`, for every finite count and positive
point precision, provided the positive step is at most the cutoff.
This mass-17 arithmetic cutoff differs from the mass-4 cutoff used in the
default evaluator. `mellin-cutoffs.lisp` now handles the latter directly:
external cell weights and a telescoping reciprocal potential bound every
sufficiently fine dyadic tail by `34*C1*(1/start-1/end)`, where
`C1 = (j+1)*(j+2)/(sigma-2)^(j+2)`. At the default cutoff requested with
error `e`, this radius is at most `17*e/4`. A computed halving depth ensures
the required mesh bound, without changing the evaluator's cutoff.

`mellin-meshes.lisp` compares partitions with unrelated rational endpoints.
When one cell ends first, its peer is trimmed while retaining the original
sample anchor. Thus each sample sum is preserved exactly. The spatial
transport theorem bounds the two anchors' samples, and summing the common
cell lengths gives error at most
`length*(L*(meshLeft+meshRight)+A*(pointErrorLeft+pointErrorRight))`.
Exact dyadic endpoint and sum identities apply this to the default
quadrature and a separately partitioned prefix and tail.

For a smaller cutoff `r` and a larger one `R`, the common fine mesh is the
minimum of `r` and
`delta/(16*(1+R*L_R+r*L_r))`; the common point precision is
`delta/(16*(1+R*A_R+r*A_r))`. ACL2 proves all budgets and computes both
partition depths. Comparing each default sum with the appropriate fine
sum, then adding the actual dyadic tail, proves

```
disk(I_h(e) - I_h(f), 5*(e+f)).
```

This holds for rational `sigma > 2`, rational height, natural index and
positive `e,f`, regardless of which cutoff is larger. Choosing each
precision at most `targetError/10` gives a difference at most `targetError`.
The proof uses finite rational samples, partition comparison and the proved
signal-tail bound; it assumes no real integral or coefficient estimate.
The kernel argument below supplies the normalized coefficient-pair bound;
the real coefficient and pole comparison remain separate obligations.

`negative-binomial.lisp` and `kernel-mass.lisp` now give the normalized
total-mass upper bound in arithmetic. Define
`R(n,j) = product_{k=1}^j (n+k)/k`. ACL2 proves Pascal's identity and
`n^j/j! <= R(n,j)`. For rational `0 <= q < 1`, the explicit potential

```
P(n,0,q) = q^n/(1-q)
P(n,j,q) = (P(n,j-1,q) + q^n*R(n-1,j))/(1-q)
```

is nonnegative and satisfies `P(n,j,q)-P(n+1,j,q)=q^n*R(n,j)`.
Its value at zero is `(1-q)^(-j-1)`, so telescoping bounds every finite
sum of these moments. No infinite-series identity is supplied as a premise.

Finite Taylor convolution also proves `(1+t)^n <= upperExp(n*t,error)`.
With `q = 1/(1+a*h)`, this bounds each lower kernel weight on the grid
`u=n*h` by `h^j*R(n,j)*q^n`. Applied to `mellin-weight` with its actual
point-dependent kernel precision, the moment bound gives

```
h * sum_{n=0}^{N-1} mellinWeight(n*h,a,j,1,error) <= (1/a+h)^(j+1).
```

The arithmetic inequality `(1+t)^k <= 2` for `2*k*t <= 1` then gives
the normalized upper bound `2/a^(j+1)` whenever `2*a*h*(j+1) <= 1`.
The grid constructor discharges that requirement: for cutoff `T > 0`
and requested maximum spacing `d > 0`, it chooses
`N = 1 + ceiling(2*a*T*(j+1) + T/d)` and `h = T/N`.
ACL2 proves `N > 0`, `0 < h <= d`, `N*h=T`, the small-mesh condition,
and the resulting mass bound, for every natural `j` and positive point
precision. This proves a finite upper bound with a conservative factor 2.

`kernel-tilts.lisp` now compares the same finite moments at two rational
ratios. If a range ends at or before address `K`, replacing `q` by
`q' <= q` costs at most `(q/q')^K`. For a range starting at or beyond `K`,
the same formula holds with `q <= q'`. Applying this with
`q_a = 1/(1+a*h)` tilts the rate-250 kernel to rates 300 and 200.
`exp-geometric.lisp` proves the resulting decay using finite Taylor sums,
repeated products and negative-binomial bounds, without a real exponential
or an infinite geometric series as an input.

Write `L,U` for the computed log endpoints and suppose
`L >= 64`, `L <= U` and `303.05*U <= j <= 312.5*L`.
On a grid with `600*h*(j+1) <= 1`, define

```
leftCount = ceiling(U/h)
rightAddress = ceiling((3*L/2-1)/h)
D_j = (79/80)^j * (1/250)^(j+1).
```

`kernel-window.lisp` bounds the actual lower-weight mass before `leftCount`
by `2*D_j` and every finite mass starting at `rightAddress` by `5*D_j`.
The derivative band discharges the needed cutoff and small-spacing checks.
The exact scale conversion

```
D_j = (126/125) * (4977/5000)^j * (1/252)^(j+1)
```

retains strict geometric decay. Let
`J = max(64, geometricIndex(5000/4977,128))` and `Y0 = 2^(2*J+9)`.
For every rational `Y >= Y0`, the constructed `windowIndex(Y)` and
`kernelGridStep(T,300,j,d)` satisfy all hypotheses. Multiplying the sum
of both tail masses by 16 still gives at most `(1/252)^(j+1)`.
Neither a band estimate nor mesh adequacy is supplied as a premise.

`kernel-window-refinement.lisp` transfers concentration to upper kernel
enclosures. Their finite sum `V(e)` uses the same unit-weight kernel
constructor, with external grid weight `h` and primitive precision `e`.
If `A = h*(leftCount+rightCount)`, ACL2 proves

```
V(e) <= 7*D_j + A*e.
```

Comparison with the actual sampler first adds `A*sampleError`. A computed
positive refinement from any putative rational excess removes that term;
no classical limit is invoked. Choosing
`e = targetError/(32*(1+A))` then proves, at the same computed window
threshold, index and mesh,

```
16*V(e) <= (1/252)^(j+1) + targetError/2.
```

`kernel-quadrature.lisp` relates these externally weighted enclosures to
the tail evaluator, whose kernel constructor includes the cell length:

```
upperKernel(u,a,j,h,e) <= h*upperKernel(u,a,j,1,E) + e.
```

The proof uses overlap of the underlying reciprocal exponential bands and
the first enclosure's width. Summing adds at most `cellCount*e`.
With `e = targetError/(32*(1+cellCount))`, the actual internally weighted
rectangles on both log-window tails satisfy
`16*rectangles <= (1/252)^(j+1) + targetError`, at the same computed window
threshold, derivative index and mesh.

The inside-window rational-power shift is now proved in
`rpow-kernel.lisp`. Finite Taylor convolution and repeated-product bounds
give, for natural `p`, positive `q`, `p <= q`, `u >= 0` and `sigma >= p/q`,

```
lowerExp(u)^p * lowerExp((sigma-p/q)*u)^q <= upperExp(sigma*u)^q.
```

All three precisions are independent. The polynomial root bracket gives
`rpowLower(x,p,q)^q <= x^p`. When `x <= 2*lowerExp(u)`, multiplication,
`2^p <= 2^q`, and integer-power order reflection therefore prove

```
rpowLower(x,p,q) * lowerKernel(u,sigma,j,h)
  <= 2*upperKernel(u,sigma-p/q,j,h).
```

The actual log-signal point satisfies that premise. This proof uses finite
rational sums and powers, rather than an analytic rpow identity or a limit.

`mellin-kernel-budget.lisp` applies the shift to the evaluator's exact
spatial window test. Its inside branch is bounded by
`2*(C+1)*upperKernel(sigma-p/q)` and its outside growth branch by
`16*upperKernel(sigma-2)`. Summing over the actual dyadic rows, with the
default improper cutoff, depth and point precision, proves `B(e) <= K(e,d)`
for the constructed shifted-kernel budget and arbitrary shifted precision
`d`. Failed search consequently gives

```
disk(I_h(e), 2*K(e,d) - Re(I_0(e)) + e/2).
```

`log-exp.lisp` now proves those spatial comparisons in arithmetic.
For rectangles starting at `a > 0` with spacing `h >= 0` and count `n`,
write `L_n,U_n` for their log endpoints. ACL2 proves

```
a + n*h <= a*Taylor(U_n,n)
a*Taylor(L_n,k) <= a + n*h       (every natural k).
```

The endpoint ratios telescope. Finite Taylor products bound the factors
`1+h/a` in the first comparison; a proved geometric barrier bounds
`Taylor(h/(a+h),k)` by `(a+h)/a` in the second. No real logarithm,
exponential inverse law or classical limit is an input.

Consequently, with the actual computed log bounds `L,U` for `Y`,
`u >= U` implies `Y <= upperExp(u) <= logSignalPoint(u,error)`.
Finite Taylor products also prove
`4*lowerExp(u)^2 <= Y^3` when `u <= 3*L/2-1`.
The evaluator's point is at most `2*lowerExp(u)`, so any sample outside
`Y <= point` and `point^2 <= Y^3` satisfies

```
u < U  or  3*L/2-1 < u.
```

For `u = address*h` with natural `address`, positive rational `h` and
`L >= 64`, the proved rational-ceiling separation gives exactly
`address < leftCount` or `rightAddress <= address`. These are the ranges
used by the concentration theorem, for every positive signal precision.

The masked majorant is now summed in `mellin-normalization.lisp`.
`kernel-upper-mass.lisp` first proves total upper mass at most
`2/a^(j+1) + count*h*primitiveError`. The inside contribution therefore
costs at most `4*(C+1)/(252-p/q)^(j+1)` before precision losses. The two
outside tails cost at most `1/252^(j+1)`, which is at most
`1/(252-p/q)^(j+1)`. All finite prefix/suffix masks are accounted for.

The resulting shifted-kernel sum has an explicit precision cost. For any
putative excess of the original finite window budget over the normalized
bound, the proof computes a positive shifted precision making that cost
at most half the excess. Thus the original budget, at any positive sample
precision, satisfies exactly

```
B_grid <= (4*C+5)/(252-p/q)^(j+1).
```

`mellin-dyadic-normalization.lisp` proves exact equality between the actual
dyadic budget and a uniform sum with count `2^depth` and spacing
`T/2^depth`. It constructs a common refinement depth by adding the two
default depths (at heights `H` and zero) to a computed depth with spacing
at most `1/(600*(j+1))`. The default point precision is retained. Each
refined coefficient differs from its default output by a disk of radius
at most `e/2`, using the proved spatial modulus and precision budgets.

The normalized budget bound on that common grid and the one-sided disk
inequality now prove, for the default improper evaluator itself,

```
disk(I_H(e), (8*C+10)/(252-p/q)^(j+1) - Re(I_0(e)) + e).
```

The threshold and derivative index are computed as above. No normalized
coefficient estimate is supplied as a hypothesis. The retained real
coefficient must still be accounted for in the pole/Cauchy comparison;
neither the pole lower bound nor the final Landau contradiction follows
from this numerical estimate alone. These conservative constants differ
from the paper draft, so its final threshold needs a compatible derivation.

The primitive evaluator properties now have arithmetic proofs too:
`log-partitions.lisp` compares arbitrary rational rectangle partitions and
proves overlap, Cauchy error and Lipschitz bounds for logs on inputs greater
than 1. `rpow-continuity.lisp` proves corresponding bounds from polynomial
brackets for powers with exponents in `[0,1]`, on inputs at least 1.
`euler-continuity.lisp` now supplies arithmetic overlap/Cauchy bounds across
different harmonic truncations and primitive precisions too. The log and
power books also prove lower-to-upper transport without an added precision
loss. These bounds are now composed into transport of the full signal.

`log-growth.lisp` proves that every rational `Y >= 2^(2*J + 9)` passes the
computed derivative-index check and produces an index at least `J`. The
composed theorem meets all three geometric targets. This discharges eventual
admission of the threshold checks. The concentration theorems above now
use that checked band and apply it to the complete finite window budget
and the default coefficient-pair bound.

## Finite Cauchy sampling

`complex-geometric.lisp` supplies rational complex reciprocals with squared
norm checks, exact geometric telescoping, and the remainder identity

```
1/(1-q) - sum_{n<N} q^n = q^N/(1-q).
```

For `disk(q,r)` with `r < 1`, the remainder has radius at most
`r^N/(1-r)`. For `disk(q,1)` with squared distance from 1 at least `delta^2`,
`delta > 0`, every finite geometric sum has radius at most `2/delta` and
its average has radius at most `2/(N*delta)` for positive `N`. These are
finite rational identities and inequalities, with no analytic series law
among the hypotheses.

`cauchy-orbits.lisp` constructs `t = 1/(2*(degree+1))` and the rational
Cayley rotation `w = (2+i*t)/(2-i*t)`. Its squared norm is exactly 1,
as is every natural power. The proved quadratic power remainder gives
`Im(w^k) >= k*t/4 >= delta`, where `delta=t/4`, for `1 <= k <= degree`.
Thus the same positive denominator gap works for every required frequency.

Define the positive-frequency moment as the geometric average of `w^k`,
and the negative-frequency moment by conjugation. The zero moment is
exactly `(1,0)`. Given positive rational error `e`, the computed count

```
N = 1 + ceiling((2/delta)/e)
```

is positive and makes every nonzero signed moment through the requested
degree lie in a disk of radius `e`. The nodes and sample count are all
computed; neither separation nor moment cancellation is supplied as a premise.

`cauchy-polynomials.lisp` evaluates a polynomial directly at those nodes,
weights each value by the conjugate of the target monomial, and averages.
It proves that this actual average equals the moment expansion

```
A_j = (1/N) * sum_{n<N} P(w^n) * conjugate((w^n)^j)
    = sum_k a_k * moment(k-j, N).
```

For degree at most `d`, coefficient mass
`B=sum_k (abs(Re(a_k))+abs(Im(a_k)))` bounds the off-diagonal error by
`B*e`. The diagonal is proved equal to the selected list coefficient `a_j`.
`cauchy-extraction.lisp` chooses `e=error/(1+B)` and computes the corresponding
positive sample count. It proves `disk(A_j-a_j,error)` for every valid
coefficient list and positive rational error.

The boundary checker evaluates `P(w^n)` at every sampled node. If it accepts
cap `M>=0` at the computed count, unit norms and finite triangle inequalities
give `disk(A_j,M)` and hence `disk(a_j,M+error)`. No coefficient estimate or
boundary supremum theorem is assumed to prove this finite result. A ground
assertion checks the conjugation sign against a separately calculated
sample average for `P(z)=1+2*i*z`.

### Rational resolvents and principal parts

`cauchy-resolvents.lisp` constructs the coefficient list
`(1,q,...,q^(m-1))` and proves that its polynomial evaluator is exactly the
finite geometric sum at `q*w`. For `disk(q,r)`, `0<=r<1`, and
`disk(w,1)`, the difference from the actual rational value
`1/(1-q*w)` has radius at most `r^m/(1-r)`. A positive truncation order
is computed: 1 when `r=0`, and otherwise

```
m0(r,e) = 1 + geometricIndex(1/r, 1/(e*(1-r))).
```

Every natural `m>=m0(r,e)` makes that error at most `e`.
This follows from finite reciprocal-power identities and the already
certified geometric threshold.

`resolvent-sampling.lisp` samples the actual rational function at the orbit
nodes. It proves that weighting and averaging preserve this uniform error.
For target `j` and requested error `e>0`, it chooses
`m=max(j+1,m0(r,e/2))`, degree `m-1`, and the polynomial coefficient
sampling count with error `e/2`. The actual resolvent's weighted average
then differs from `q^j` by at most `e`. Both errors are derived from the
evaluators; no infinite-series identity is an input.

`pole-resolvents.lisp` evaluates the actual principal part `c/(a-R*w)`.
For rational complex `a!=0` and `c`, write `q=R/a` and `b=c/a`.
Exact rational identities reduce this function to `b/(1-q*w)`.
Given a checked `disk(q,r)` with `r<1`, the constructor requests
resolvent coefficient error `e/(1+L1(b))`, where
`L1(b)=abs(Re(b))+abs(Im(b))`. Multiplication by `b` then gives total
error at most `e`. The recovered coefficient is proved equal to

```
b*q^j = c*R^j/a^(j+1).
```

The variable is `z-R*w`, matching the sign in Landau's coefficient
`A_j`. A checked lower distance `L>0`, `L^2<=normSquare(a)`,
with `0<=R<L`, supplies nonzero `a` and the explicit ratio bound
`disk(q,R/L)`, `R/L<1`. Ground assertions independently check complex
principal-part values, the radius power, and the weighting sign.

### Residue constraints and finite pole families

`pole-lower.lisp` reconstructs the residue from the explicit unscaled
coefficient `P_j=c/a^(j+1)`: exactly `a^(j+1)*P_j=c`. Hence
`disk(a,d)` and `disk(P_j,B)` imply `disk(c,d^(j+1)*B)`.

`zeta-pole-lower.lisp` computes the residue
`c=-nu/(rho*(rho-1))` for positive integer multiplicity `nu`.
Its exact denominator identity gives

```
disk(rho,M1), disk(rho-1,M2), disk(c,B)
    => nu <= M1*M2*B.
```

Combining cancellation with the finite Cauchy theorem derives a lower
constraint for a pole plus a polynomial remainder. If the remainder's
computed boundary checker accepts cap `M` with coefficient error `e`,
and the combined coefficient has cap `B`, then

```
nu <= M1*M2*d^(j+1)*(B+M+e).
```

The residue formula and multiplicity supply this constraint; no lower
coefficient estimate is assumed.

`zeta-pole-sums.lisp` uses a finite list of entries `(rho . nu)`,
retaining a positive multiplicity for every recorded location. It computes
`mass=sum L1(-nu/(rho*(rho-1)))`. A clearance checker verifies
`R^2<=normSquare(center-rho)` for every other pole. These finite checks
prove that the sum of the other coefficients lies in a disk of radius
`mass/R^(j+1)`.

`pole-dominance.lisp` computes an index from the separation ratio
`d/R<1` and the scaled mass `M1*M2*mass`, using the certified resolvent
truncation count. At and above that index, the other poles consume at most
one half of the residue budget. The selected pole's positive integer
multiplicity then forces

```
1/2 <= M1*M2*B*d^(j+1).
```

A second theorem includes a polynomial remainder checked by the actual
finite Cauchy boundary evaluator. With normalized `d<1` and `d<R`,
a computed maximum of two indices makes the other poles and polynomial
remainder consume at most one quarter each. It obtains the same lower
constraint for the full combined coefficient. Ground checks exercise
multiple locations and multiplicities, acceptance and rejection of
clearances, and the actual index constructor.

`pole-radius-dominance.lisp` removes the unit-distance restriction.
A regular polynomial on the physical contour `z=R*w` contributes its
j-th unit-variable coefficient divided by `R^j`. For `d<R` and
`d<clearance`, a computed maximum of two indices absorbs the other poles
and this rescaled regular part into quarter budgets, giving the same
`1/2 <= M1*M2*B*d^(j+1)` constraint. The zero arguments in
`-nu/(rho*(rho-1))` are unchanged.

### Finite Mellin moment comparison

`complex-exp.lisp` defines the rational complex Taylor term and sum

```
T_0(z)=1, T_(n+1)(z)=z*T_n(z)/(n+1), E_n(z)=sum_(k<=n) T_k(z).
```

For `disk(z,R)`, it proves `disk(T_n(z),expTerm(R,n))` and bounds every
later finite-sum difference by `2*expTerm(R,n+1)` once `2R<=n+2`.
The evaluator uses the existing computed real exponential index with the
rational cap `L1(z)`. Its Cauchy bound is `leftError+rightError`.
At nonnegative real inputs it equals the lower endpoint of the existing
real exponential evaluator exactly.

A common later sum allows a uniform Taylor order on `disk(z,R)`,
independently of the evaluator's point-specific L1 cap:
`E_(expIndex(R,e/2))(z)` differs from the complex evaluator at precision
`e/2` by at most `e`. The exact moment identity is also proved:

```
T_j(u*w) = (u^j/j!)*w^j.
```

`kernel-moments.lisp` compares the actual kernel bands at indices `j`
and 0. Their defining negative-exponential bands overlap after multiplying
the zeroth band by `t=expTerm(u,j)`. Consequently, their lower endpoints
satisfy `abs(weight_j(e)-t*weight_0(f))<=e+t*f`.

`mellin-moments.lisp` carries that identity through the actual signal and
phase evaluators, without an assumed analytic kernel. Write
`m=h*expTerm(u,j)` and let `G` be the existing computed signal cap.
The explicit error factor is

```
K = m + G*(1+expTerm(u,j)) + G*m.
```

The cross-index sample error is at most `K*(leftError+rightError)`.
Choosing primitive precision `delta=e/(2*(1+K))` proves that the existing
j-th sample differs from `expTerm(u,j)*sample_0(delta)` by at most `e`.

`mellin-taylor-grid.lisp` sums these node comparisons on the existing
finite grid. For `N` cells and requested error `e`, it compares the
standard quadrature with budget `e/2` to a sum of factorial-weighted
zeroth samples. Each node's target comparison budget is
`e/(4*(N+1))`; the primitive precision is computed from that node's
factor `K`. The total difference is at most `e`. The base precision
is chosen for the target moment; it can then be held fixed while building
a Taylor polynomial for that moment.

### Explicit Mellin grid polynomials

`exp-polynomials.lisp` constructs an actual coefficient list for a finite
mixture of nodes `(u_k . b_k)`. Its coefficients and evaluation satisfy

```
a_l = sum_k b_k*u_k^l/l!,
P_D(w) = sum_(l<=D) a_l*w^l = sum_k b_k*E_D(u_k*w).
```

Both identities are proved for the recursive list and polynomial
evaluators. A hand-calculated two-node example checks complex amplitudes,
factorials and evaluation at an imaginary argument.

`exp-mixture-bounds.lisp` computes a degree and every evaluation precision.
For `N` nodes, requested error `e>0`, disk radius `R>=0` and target
index `j`, it chooses

```
eta = e/(N+1),
delta_k = eta/(2*(1+L1(b_k))),
D = max(j, max_k expIndex(u_k*R,delta_k)).
```

The polynomial `P_D` differs from
`sum_k b_k*complexExpValue(u_k*w,delta_k)` by at most `e` throughout
`disk(w,R)`. The real Taylor tail and the complex evaluator precision
each contribute at most `delta_k` before amplitude scaling.

`mellin-polynomials.lisp` constructs these nodes from the actual Mellin
grid. For the target moment `j`, it freezes each zeroth-moment sample at
the node precision already computed by `mellin-taylor-grid.lisp`.
Every coefficient of the resulting polynomial uses those same node
amplitudes. The selected coefficient is exactly the factorial-weighted
sum compared with the existing quadrature; its evaluation is the explicit
finite Taylor mixture above. The wrapper also computes a degree giving
uniform mixture approximation.

The finite Cauchy theorem now applies to that polynomial. With polynomial
budget `e/2`, an accepted boundary cap `M` using Cauchy coefficient error
`e/2` proves that the existing finite quadrature at budget `e/4` lies
in `disk(M+e)`. The proof derives the coefficient estimate from the
checker and the actual grid comparison.

### Complex multiplication and reciprocal agreement

`complex-convolution.lisp` proves the exact complex Taylor row and triangle
identities from the term recurrence. In particular, the full degree-n
convolution row is `T_n(z+w)` and the full total-degree triangle is
`E_n(z+w)`. No exponential addition law is an input.

`complex-exp-product.lisp` bounds the difference between the product
rectangle and that triangle by the corresponding nonnegative real
difference. For `disk(z,Rz)`, `disk(w,Rw)` and
`2*(Rz+Rw)<=n+2`, this gives

```
disk(E_n(z)*E_n(w)-E_n(z+w), 2*expTerm(Rz+Rw,n+1)).
```

The same book computes `C(z)=upperExp(L1(z),1)`, proves `C(z)>=1`,
and bounds every Taylor prefix and evaluated value by that cap.

`complex-exp-multiply.lisp` constructs one common Taylor order above the
three evaluator indices and the real product-tail index. The resulting
evaluated multiplication law is

```
disk(X(z,eL)*X(w,eR)-X(z+w,eS), C(w)*eL+C(z)*eR+2*eS).
```

Here `X` is the computed complex Taylor evaluator. All precisions are
positive rationals; the common order and magnitude caps are computed.

`complex-exp-negative.lisp` applies this law to `x+(-x)=0`.
The positive real evaluator is the lower endpoint of the existing real
exponential band and is at least 1. Dividing the computed product error by
that endpoint, then comparing reciprocal-band endpoints, proves for
`x>=0`

```
disk(X(-x,e)-(lowerExpNeg(x,f),0), (3+2*C(x))*e+f).
```

The constructor `delta=error/(5+2*C(x))` makes this difference at most
`error` when both primitive precisions are `delta`. Thus the negative
real Taylor evaluator and the reciprocal primitive already used by the
Mellin kernel are connected by a proved error budget. Independent ground
checks verify a complex truncated-product difference and the exact
negative-real and reciprocal values at Taylor order 7.

`complex-exp-phase.lisp` compares a Cayley rotation with the imaginary
Taylor evaluator using its degree-one prefix. For `|a|<=1` the error is
at most `3*a^2/2+e`. A rotation lies exactly in the unit disk, so the
evolution comparison accumulates errors linearly rather than requiring a
growing product of magnitude caps. Put

```
E(t) = 1 + upperExp(|t|,1).
```

For any positive integer `n>=|t|`, the existing grid and phase-value
comparison, combined with this evolution estimate, proves

```
disk(X(i*t,eX)-phase(t,eP),
     (1+3*E(t)/2)*t^2/n + n*(3*E(t)+2)*eX + eP/2).
```

`complex-phase-agreement.lisp` makes the choices explicit:

```
N = 1 + max(fuel(|t|,1), fuel(8*(1+E(t))*t^2,error))
A = 1 + N*(3*E(t)+2)
delta = error/(4*A).
```

For rational `t` and positive rational `error`, `N` is a positive
integer, `delta` is a positive rational, and
`disk(X(i*t,delta)-phase(t,delta),error)`. The proof applies to either
sign of `t`; exact ground checks exercise both signs and the factorial
in the degree-four imaginary Taylor sum.

`complex-damped-phase.lisp` then composes the two primitive comparisons.
For `x>=0`, rational `t`, and positive rational `error`, define

```
eta = error/(4*(1+C(x)+C(i*t)))
deltaN = eta/(5+2*C(x))
deltaP = phaseComparisonPrecision(t,eta)
D = lowerExpNeg(x,deltaN) * phase(t,deltaP).
```

The computed theorem proves `disk(D-X(-x+i*t,eta),error)`.
It uses the multiplication law at the two orthogonal arguments and
explicitly pays for both component comparisons.

`complex-kernel-agreement.lisp` removes the restriction to those particular
primitive precisions. For independent positive rational precisions
`eN,eP,eX`, it proves

```
disk(lowerExpNeg(x,eN)*phase(t,eP)-X(-x+i*t,eX), eN+eP+eX).
disk(X(-x+i*t,eX), 1+eX).
```

The first comparison is initially proved with an arbitrary positive
auxiliary margin. `complex-disk-gap.lisp` eliminates that margin by
finite rational arithmetic: if a point of squared norm `Q` is outside
the disk of nonnegative radius `r`, then

```
d = (Q-r^2)/(4*(1+Q+r))
```

is positive and the point remains outside the disk of radius `r+d`.
Instantiate the proved comparison at that computed margin to obtain a
contradiction. No analytic limit, choice operation or additional axiom
is an input to this argument.

`mellin-exponential-sample.lisp` now applies the independent-precision
comparison to the actual sampler. At rational `u,sigma,h>=0`, rational
height `H`, and natural moment index `j`, let `s` be the signal value at sample precision
`a`, and let `m=h*u^j/j!` be its exact mass factor. Its negative and
phase precisions `n,p` are the existing constructor outputs, each at
most `a`. With positive complex precision `b`, define

```
E_j(a,b) = s*m*X(-sigma*u-i*H*u,b).
```

The proved comparison is

```
disk(MellinSample_j(a)-E_j(a,b), |s|*m*(n+p+b)).
```

Writing `M=signalCap(u)` and `F=1+2*M*m`, the radius is at most
`F*(a+b)`. Thus the explicit common precision
`delta=error/(2*(1+F))` proves
`disk(MellinSample_j(delta)-E_j(delta,delta),error)`.
The signal value and mass factor are retained in this conclusion.
The same book also proves that signal samples using different nonnegative
abscissas differ by at most the sum of their requested sample precisions.

`mellin-shift-bounds.lisp` computes a magnitude cap for the entire shift
disk. For `disk(w,R)` and `u>=0`, put

```
B = 1+upperExp(2*u*R,1)
C = C(-sigma*u-i*H*u)
S = signalCap(u)*m
F = 1+2*S
K = 1+2*F*(1+B)+S*(B+C+2)+4*m.
```

The bound `C(u*w)<=B` follows from `L1(w)<=2*R`, band width and
monotone overlap. `K` is positive and independent of the chosen point
`w`. `mellin-sample-shift.lisp` proves, when `sigma-Re(w)>=0`
and `0<delta<=1`,

```
disk(MellinSample(sigma,H,j,delta)*X(u*w,delta)
     -MellinSample(sigma-Re(w),H-Im(w),j,delta), K*delta).
```

It accounts for both sample/exponential comparisons, exponential
multiplication and the signal precision change. The common precision
`delta=min(1,error/(1+K))` makes the radius at most `error` throughout
the checked disk.

`mellin-shift-mixture.lisp` freezes each zeroth-moment base sample at
a precision bounded by that shift precision, the target moment precision,
`q`, and `q/(4*(1+sampleCap))`. The target moment only affects the
precision choice. The same base is used at every evaluation point and in
every polynomial coefficient.

The mixture evaluator chooses its own exponential precision
`q/(2*(1+L1(base)))`. A proved Cauchy comparison accounts for that
difference. For `N` cells, mixture budget `q>0` and quadrature point
precision `a>0`, the comparison with actual shifted zeroth-moment
quadrature has radius at most `N*(3*q+a)`. Choosing
`q=error/(8*(N+1))` and `a=error/(4*(N+1))` gives a radius at most
`error`.

The same book constructs one polynomial `P` with those frozen base
samples and a computed Taylor degree. For `R<=sigma`, its final uniform
comparison is

```
disk(P(w)-mellinSum(cells,sigma-Re(w),H-Im(w),0,error/8),error)
    whenever disk(w,R).
```

This is a comparison with the existing finite quadrature.
`mellin-shift-coefficients.lisp` now uses the same frozen bases for the
selected moment. Its node precision is at most the computed moment
precision, so the moment-pair error is at most `q`. Cauchy comparison
with an arbitrary sample precision `a` gives node error `a+2*q`;
summing gives `N*(a+2*q)`.

For the polynomial constructed at error `e`, this proves

```
disk(mellinSum(cells,sigma,H,j,e/8)-coefficient(P,j),e/2).
```

Combining this with the accepted finite Cauchy boundary check, using its
computed count and extraction precision `e/2`, gives
`disk(mellinSum(cells,sigma,H,j,e/8),M+e)`.
The polynomial used for the coefficient comparison is the same one used
for the uniform shifted-quadrature comparison.

`mellin-sample-scaling.lisp` connects the two quadrature conventions.
For independent positive precisions `a,b` and nonnegative cell width
`h`, it proves

```
disk(sample(u,sigma,H,j,h,a)-h*sample(u,sigma,H,j,1,b),a+h*b).
```

A coarse comparison follows from the exponential representation and signal
transport across step parameters. A computed positive refinement budget,
then the rational disk-gap argument, removes its auxiliary error.
No homogeneity law for an unspecified analytic kernel is assumed.

`mellin-dyadic-cells.lisp` constructs the exact dyadic partition as a
cell list. Its total mass is the interval width. A cell list of length
`N` and total width `U` satisfies

```
disk(cellSumRaw(a)-weightedUnitStepSum(b),N*a+U*b).
```

For the default finite sum constructor this becomes `e+U*b`.
Comparing the same partition with the bounded integral constructor at
precision `f` yields radius at most

```
e + U*spatialSlope(U,sigma,H,1)*mesh + f.
```

If the partition is exactly the constructor's own depth, the sharper
radius is `e+f/4`.

`mellin-integral-polynomial.lisp` uses precisely the cutoff and depth of
the default improper evaluator at precision `e`. The corresponding
finite cell sum at precision `g` differs from that evaluator by at most
`g+e/8`. Construct the shift polynomial on those cells at precision
`e/4`. An accepted boundary cap `M`, with the computed Cauchy count
and extraction precision `e/8`, then proves

```
disk(mellinIntegral(sigma,H,j,e),M+e).
```

`mellin-cutoff-order.lisp` proves that the actual cutoff decreases as
the abscissa increases. Its coefficient is a positive multiple of a power
of the reciprocal decay rate; the bounded rational ceiling is monotone.
For `U>=defaultCutoff(sigma,j,b)` it also proves

```
disk(boundedIntegral(U,sigma,H,j,a)-mellinIntegral(sigma,H,j,b),
     5*(a+b)).
```

The proof uses the existing split/prefix refinements and the arithmetic
tail bound at the default cutoff.

`mellin-uniform-mesh.lisp` bounds the spatial slope throughout a rational
rectangle `0<=sigma'<=S`, `|H'|<=T`. It accounts for the possible
one-unit loss when comparing exponential upper bands at different
arguments. A computed halving depth then controls every shift in the disk
using `S=sigma+R` and `T=|H|+R`; the depth is independent of the
evaluation point.

`mellin-improper-polynomial.lisp` assembles these results. For
`sigma-R>2`, target moment `j` and positive error `e`, choose

```
epsilon = e/64
sigmaMin = sigma-R
U = max(defaultCutoff(sigmaMin,0,epsilon),
        defaultCutoff(sigmaMin,j,epsilon)).
```

A fixed dyadic mesh makes `U*spatialSlope*mesh<=e/16` throughout the
shift disk. On those cells construct the shift polynomial at precision
`e/4`. The common quadrature differs from the actual improper output,
for moments 0 and `j`, by at most `17*e/64`. Consequently the same
computed polynomial `P` satisfies

```
disk(P(w)-mellinIntegral(sigma-Re(w),H-Im(w),0,epsilon),e)
    whenever disk(w,R).
disk(mellinIntegral(sigma,H,j,epsilon)-coefficient(P,j),e/2).
```

Its cutoff, mesh and base samples are fixed across the disk. An accepted
finite Cauchy boundary cap `M`, with the computed sample count and
extraction precision `e/2`, proves
`disk(mellinIntegral(sigma,H,j,epsilon),M+e)`.
The Cauchy routine samples the unit circle; using the uniform improper
comparison at those sample points additionally requires `R>=1`.

This constructs the numerical family within the convergence half-plane.
Finite exponential mixtures cannot supply meromorphic continuation beyond
that region by merely increasing the cutoff.

### Computed exponential integration basis

`complex-exp-increment.lisp` gives uniform first-order estimates for the
actual rational complex exponential evaluator `E(z,delta)`. Write

```
U(M) = 1 + upperExpBound(M,1).
```

For `L1(z)<=M`, `U(M)` bounds the evaluator and its internal cap.
For `disk(z,r)` with `r<=1`, the first-order error is at most
`r^2+delta`. The proved exponential multiplication law then controls
each finite rectangle defect.

`complex-exp-grid.lisp` sums these defects by exact finite telescoping.
Let `K=L1(z)`, let all grid abscissas lie in `[0,bound]`, choose
`D>=K*bound`, and assume `K*h<=1`. For `n` rectangles of width `h`,
the endpoint expression

```
F(z,a,b,delta) = (E(b*z,delta)-E(a*z,delta))/z
```

differs from the evaluated left rectangle sum by at most

```
n * (U(D)*K^2*h^2 + Q*delta) / c,
Q = U(1)+2*U(D)+2,
```

where `c>0` is a checked lower norm bound for `z`. Comparing two
endpoint precisions costs at most `2*(deltaLeft+deltaRight)/c`.
These are bounds on finite computations, derived without assuming an
analytic integral formula.

`complex-exp-integral.lisp` computes sufficient parameters. For start
`a>=0`, length `L>0`, clearance `c>0` and requested error `e>0`,
set `D=K*(a+L)` and use the existing rational precision-fuel constructor:

```
n = 2 + fuel(K*L,1) + fuel(4*U(D)*K^2*L^2,c*e)
h = L/n
delta = min(c*e/16, c*e/(16*n*Q))
eta = c*e/16.
```

The book proves all range, positivity and budget conditions. The grid at
precision `delta` differs from `F(z,a,a+L,eta)` by at most `e`.
The latter evaluator has Cauchy radius `(eLeft+eRight)/8`.

`complex-laplace-basis.lisp` handles the infinite endpoint. The existing
damped-phase comparison and finite exponential lower bounds give

```
disk(E(-v+i*t,delta), 1/(1+v)+2*delta),  v>=0.
```

For rational `sigma>0`, rational height `H` and error `e>0`, choose

```
T = 1 + fuel(4,sigma^2*e).
```

The cutoff meets `4<=T*sigma^2*e`. Apply the computed finite integration
routine on `[0,T]` to `z=-sigma-i*H`, at requested error `e/4`.
The theorem `lw-complex-laplace-grid-reciprocal` proves that this actual
finite grid sum differs from `1/(sigma+i*H)` by at most `e`.
It includes the cutoff tail, evaluation error and mesh error.

The first-moment basis handles the additional factor `u` needed by the
logarithmic correction. `complex-exp-moment-grid.lisp` derives its finite
integration-by-parts expression from weighted rectangle defects:

```
F1(z,a,b,delta) = (b*E(b*z,delta)-a*E(a*z,delta)-F(z,a,b,delta))/z.
W = bound+1/c
```

Under the same grid conditions, the error against
`sum_{k<n} h*(a+k*h)*E(z*(a+k*h),delta)` is at most

```
n * (U(D)*(W*K^2+K)*h^2 + W*Q*delta) / c.
```

Changing endpoint precision costs at most
`2*W*(deltaLeft+deltaRight)/c`. The computed routine in
`complex-exp-moment-integral.lisp` uses `bound=a+L`, and sets

```
A = U(D)*(W*K^2+K)
B = W*Q
n = 2 + fuel(K*L,1) + fuel(4*A*L^2,c*e)
h = L/n
eta = c*e/(16*W)
delta = min(eta,c*e/(16*n*B)).
```

The actual finite weighted grid differs from `F1(z,a,a+L,eta)` by at
most `e`. Its endpoint evaluator has Cauchy radius
`(eLeft+eRight)/8`.

`complex-laplace-moment.lisp` proves the stronger decay estimate

```
disk(E(-v+i*t,delta), 1/(1+v/2)^2+2*delta), v>=0.
T = 1 + fuel(1,sigma) + fuel(32,sigma^3*e).
```

The cutoff guarantees `sigma*T>=1` and `32<=sigma^3*T*e`.
Apply the first-moment quadrature on `[0,T]`, at error `e/4`.
`lw-complex-laplace-moment-grid-reciprocal-square` proves that the resulting
finite weighted sum differs from `1/(sigma+i*H)^2` by at most `e`, including
its weighted endpoint tail.

`complex-laplace-ramp.lisp` treats the unshifted ramp. For complex rational
`l,r`, it computes

```
delta = e/(4*(1+expCap(l)+expCap(r)))
```

and bounds the difference between `(E(l,delta)-1)*E(r,delta)` and
`E(l+r,delta)-E(r,delta)` by `e`. Setting `l=u` and `r=-s*u`
gives the decomposition of `(exp(u)-1)*exp(-s*u)`.

For rational `sigma>1`, `s=sigma+i*H`, it constructs

```
rampValue(s,e) = laplaceGrid(sigma-1,H,e/4)-laplaceGrid(sigma,H,e/4).
```

The exact reciprocal difference is `1/(s*(s-1))`.
`lw-complex-laplace-ramp-reciprocal` proves that the constructed difference
of finite quadratures is within `e` of that value.

These establish the exponential, first-moment and unshifted ramp bases.
The shifted, assembled and evaluated logarithmic-derivative comparisons
are proved below. Their analytic interpretation remains open.

### Logarithmic correction in the actual signal

`log-exp-inverse.lisp` proves that every positive-order Taylor sum has
slope at least one on nonnegative rational arguments. Comparing finite
Taylor sums with both logarithm rectangle sums gives an arithmetic inverse
bound. If `x>=1`, `u>=0`, and

```
lowerExp(u,e) <= x <= upperExp(u,e)+slack,
```

both endpoints of `logBounds(x,eta)` differ from `u` by at most
`e+slack+eta`. No analytic inverse identity is an input.

For the existing signal point `x=logSignalPoint(u,E)`, let
`delta=logSignalDelta(u,E)` and let `epsilon` be the actual primitive
precision used by its signal evaluator. The book constructs

```
linearValue(u,E) = lowerSmoothedSum(x,signalCount(x),epsilon)
                  - x*u + x*(1+lowerEuler(epsilon)).
```

The two logarithm endpoints are within `2*delta+epsilon` of `u`.
The existing constructor budgets prove
`x*(2*delta+epsilon)+logSignalMargin(u,E)<=E`.
`lw-log-signal-computed-linearization` therefore bounds the difference
between `linearValue(u,E)` and the lower endpoint of the actual
`logSignalBounds(u,E)` by `E`. The prime sum and Euler approximation here
are the ones already used by the default signal evaluator.

### Shifted ramps and logarithmic breakpoints

`complex-laplace-shifted.lisp` extends the exponential quadrature to any
rational start `a>=0`. At positive rate `r`, height `H` and requested error
`e`, its finite grid differs from `E((-r-i*H)*a,r*e/64)/(r+i*H)` by at most
`e`. It uses the existing computed cutoff; starting farther to the right
only reduces the damped tail.

`exp-log-ramp.lisp` controls the breakpoint itself. For `n>1`, logarithm
precision `0<eta<=1` and exponential precision `epsilon>0`, write
`a=lowerLog(n,eta)` and `S(n)=expLipschitzCap(n)`. It proves

```
lowerExp(a,epsilon) <= n
abs(lowerExp(a,epsilon)-n) <= S(n)*eta+2*epsilon.
```

Define the signed extension `R(u,x,n,eta)` as zero when `u<a`, and
`x/n-1` otherwise. If `u>=0` and
`lowerExp(u,epsilon)<=x<=upperExp(u,epsilon)+slack`, with `slack>=0`, then

```
abs(max(0,x/n-1)-R(u,x,n,eta))
  <= (S(n)*eta+3*epsilon+slack)/n.
```

This includes points on either side of the rounded breakpoint. Applied to
the actual signal point, the bound is `(S(n)*eta+4*signalDelta(u,E))/n`.

`complex-log-ramp.lisp` normalizes the shifted endpoint. For
`s=r+i*H`, `r>1`, put `c=r-1`, `K=r+abs(H)` and use the earlier compact
exponential cap `U`:

```
A = U(K*n)+U(n)+2
C = (128+A+2*S(n))*(1+1/c+1/r)
delta = min(1,e/(4*C))
a = lowerLog(n,delta).
```

The exponential residual satisfies

```
disk(E((1-s)*a,delta)-n*E(-s*a,delta),
     (A+2*S(n)+4)*delta).
```

The computed value is the difference of two actual shifted quadratures:

```
V = shiftedGrid(c,H,a,64*delta/c)/n
    - shiftedGrid(r,H,a,64*delta/r).
```

Both endpoint precisions are exactly `delta`. The final theorem
`lw-complex-log-ramp-computed-normalization` proves

```
disk(E(-s*a,delta)/(s*(s-1))-V,e).
```

The start, precisions, mesh and cutoff errors are computed. The target
contains the numerical exponential at the computed logarithm; it is not
an assumed exact value of `n^(-s)`. The finite weighted signal assembly,
its interchange with Mellin quadrature, and normalization at independently
fixed logarithmic cutpoints are proved below. The later boundary-decay
and Mellin–Dirichlet comparison sections complete the connection to the
computed series in `sigma>3`.

### Fixed finite exponential family for the actual signal

`smoothed-ramp-sums.lisp` assembles the breakpoint bounds with the actual
lower Mangoldt coefficients. The `n=1` term vanishes exactly. For total
count `N` and requested error `e>0`, choose

```
q = e/(16*(1+N))
eta_n = min(1,q/S(n)).
```

Then `S(n)*eta_n<=q`. With `k` terms and any positive Mangoldt precision,
replacing the positive-part ramps at the actual signal point by the signed
extensions above costs at most `k*(q+4*signalDelta(u,E))`.

For a rational log interval `0<=u<=U`, set
`X=logSignalSpatialCap(U)` and `N=signalCount(X)`. The book proves that
`N` covers every signal point at every positive precision; padded-sum
stability identifies it with the evaluator's own count. Choosing
`E=e/(64*(1+N))` discharges the aggregate breakpoint budget. Together with
the proved logarithmic correction, this gives the full finite ramp
decomposition within `e` of the actual signal's lower endpoint.

`signal-exponential-decomposition.lisp` additionally fixes all coefficients
and replaces the signal point by the exponential evaluator. Define

```
C = 1+2*(N+1)*X+4*N+3*(N+U+3)
beta = min(1,e/(16*C))
a_n = lowerLog(n,eta_n)
y(u) = lowerExp(u,beta).
```

The resulting computed family is

```
F(U,u,e) = sum_{n=2}^N lowerMangoldt(n,beta)
                      * (if u<a_n then 0 else y(u)/n-1)
           - u*y(u) + (1+lowerEuler(beta))*y(u).
```

Here `N`, `beta`, the Mangoldt/Euler approximations and every `a_n` are
independent of the node `u`. The proof controls changes of Mangoldt
precision through the actual smoothed-sum enclosures, changes of Euler
precision, and the replacement of the signal point by `y(u)`.
For every rational `u` in the interval and independent signal precision
`epsilon>0`, `lw-signal-exponential-independent-error` proves

```
abs(lowerLogSignal(u,epsilon)-F(U,u,e)) <= epsilon+e.
```

### Global growth and computed tails of the frozen family

`signal-exponential-growth.lisp` proves, for every rational `u>=0`,
including `u>U`,

```
abs(F(U,u,e)) <= 4*lowerExp(u,beta)^2+e.
```

If `0<e<=1`, the right side can be replaced by
`5*lowerExp(u,beta)^2`. The bound is independent of the number of retained
prime terms. The proof bounds the signed extensions by the actual positive
ramps and absorbs their negative errors using the constructor's budget.

`mellin-frozen-tail.lisp` uses the same weight and phase as the actual Mellin
sampler, replacing only its signal by `F`. For rational `sigma>2`, moment
index `j`, and requested tail error `tau>0`, compute

```
T = mellinTailCutoff(sigma-2,j,5,tau).
```

For any rational `A>=T`, `0<h<=A`, natural count `m`, `0<e<=1`, and any
positive sample precision `xi`, its finite uniform tail sum satisfies

```
disk(sum_{k=0}^{m-1} frozenSample(U,A+k*h,sigma,H,j,h,e,xi), tau).
```

The cutoff is independent of `U`, the truncation, `e`, and `xi`. For a
chosen endpoint `B>T` and mesh bound `mu>0`, the book also computes

```
m = 1+precisionFuel(B-T,min(T,mu))
h = (B-T)/m.
```

It proves `m>0`, `0<h<=min(T,mu)`, `T+m*h=B`, and the same tail bound for
the resulting grid. These are finite arithmetic bounds; no improper
integral is assumed.

### Transfer to bounded Mellin quadrature and finite linearity

Write `K(U,h)=kernelSpatialCap(U,h)`. For independent positive model error
`e` and sample error `xi`, `mellin-frozen-quadrature.lisp` proves

```
disk(actualSample(u)-frozenSample(U,u), K(U,h)*(xi+e))
```

on `0<=u<=U`. On any dyadic refinement of `[a,b]` with
`0<=a<=b<=U`, the corresponding weighted sums satisfy

```
disk(actualDyadic(a,b,d)-frozenDyadic(U,a,b,d),
     (b-a)*K(U,1)*(xi+e)).
```

For requested total error `E>0`, retain the existing constructor's
`d=integralDepth(U,sigma,H,E)` and `xi=integralPrecision(U,E)`, and choose
the single model precision `chi=min(1,xi)`. The proved joint budget is

```
U*K(U,1)*(xi+chi) <= E/2.
disk(boundedMellin(U,sigma,H,j,E)-frozenBounded(U,sigma,H,j,E), E/2).
```

Here `sigma>=0`, `H` is rational, and `j` is natural. All coefficients and
breakpoints of the family `F(U,u,chi)` stay fixed across nodes, depth, and
moment index. In particular `0<chi<=1` also supplies the tail hypothesis.

`mellin-frozen-linearization.lisp` distributes this quadrature exactly over
the finite sum. If `Q` denotes the same weighted dyadic operator and
`y(u)=lowerExp(u,beta)`, it proves

```
Q(F) = sum_{n=2}^N lowerMangoldt(n,beta)*Q(extension_n)
       - Q(u*y(u)) + (1+lowerEuler(beta))*Q(y(u)).
```

This is equality of the computed rational pairs, with every threshold
test retained. Thus the explicit component sum also approximates the
existing bounded Mellin constructor within `E/2`. On an interval ending
strictly before `a_n`, `Q(extension_n)=0`. On an interval starting at or
after `a_n`,

```
Q(extension_n) = Q(y)/n-Q(1).
```

### Inserting all logarithmic breakpoints

`mellin-frozen-cutpoints.lisp` inserts a rational cutpoint `a` into each
dyadic leaf `[v,w]`: omit leaves ending at or before `a`, and otherwise
sample on `[max(v,a),w]`. Let `Q_a` denote this clipped quadrature and
`h_d=halvedWidth(b-a0,d)` the original mesh on `[a0,b]`. The sum of the
clipped widths of cells satisfying `v<a<w` is at most `h_d`, independently
of depth. The computed jump at a logarithmic cutpoint satisfies

```
J_n = abs(lowerExp(a_n,beta)/n-1)
J_n <= (S(n)*eta_n+2*beta)/n.
disk(Q(extension_n)-Q_{a_n}(extension_n), h_d*K(U,1)*J_n).
Q_{a_n}(extension_n) = Q_{a_n}(y)/n-Q_{a_n}(1).
```

The comparison applies to the actual weighted dyadic operators at any
positive sample precision. The clipped ramp identity is exact.

`mellin-frozen-cutpoint-sums.lisp` retains the actual lower Mangoldt
coefficients. Their coarse bound `0<=lowerMangoldt(n,beta)<=n` gives

```
sum_{n=2}^N lowerMangoldt(n,beta)*J_n <= N*(q+2*beta).
```

For the family's computed `N`, `eta_n` and `beta`, the existing precision
budget bounds this sum by the model error `e`. Thus, writing

```
L_clip = sum_{n=2}^N lowerMangoldt(n,beta)*Q_{a_n}(extension_n)
         - Q(u*y(u)) + (1+lowerEuler(beta))*Q(y(u)),
```

the book proves

```
disk(Q(F)-L_clip, h_d*K(U,1)*e).
```

With the bounded constructor's native depth and precision, and its frozen
model precision `chi=min(1,xi)`, the extra insertion error is at most
`E/2`. Composing it with the earlier frozen-family comparison yields

```
disk(boundedMellin(U,sigma,H,j,E)-clippedBounded(U,sigma,H,j,E), E).
```

All indices, precisions, thresholds and sums in this comparison are
computed.

### Endpoint formulas on clipped dyadic grids

`complex-exp-dyadic-grid.lisp` evaluates the complex Taylor exponential
directly on those clipped leaves. Write `E(z,delta)` for the rational
complex evaluator, take rational `A>=0`, `L>=0`, `B=A+L`, and cutpoint
`a>=0`. At depth `d`, let `h=halvedWidth(L,d)` and let `N` be the computed
dyadic leaf count. The book proves `N*h=L`. Its grid sum is

```
T_d(delta) = sum_{leaves [v,w] with w>a}
              (w-max(v,a))*E(z*max(v,a),delta).
P(delta) = (E(z*max(B,a),delta)-E(z*max(A,a),delta))/z.
```

The endpoint increments telescope exactly, including shortened and empty
leaves. For a rational complex rate `z`, rational clearance `c>0` with
`c^2<=normSquare(z)`, define

```
t = complexL1(z)
R = t*B
U = complexExpUniformCap(R)
Q = complexExpUniformCap(1)+2*U+2.
```

If `t*h<=1`, the proved finite arithmetic error is

```
disk(P(delta)-T_d(delta), N*(U*t^2*h^2+Q*delta)/c).
```

For any two positive node precisions, the same grid also satisfies

```
disk(T_d(delta1)-T_d(delta2), L*(delta1+delta2)).
```

This precision bound does not grow with depth.
`complex-exp-dyadic-integral.lisp` computes the remaining choices from the
requested error `e>0`:

```
W = (t+U*t^2*L)*L
eta = min(1,c*e/4)
d = halvingDepth(W,eta,precisionFuel(W,eta))
delta = c*e/(16*(1+N*Q))
tau = c*e/16.
```

It proves `t*h<=1`, `U*t^2*L*h<=c*e/4`, and
`N*Q*delta<=c*e/16`. These give

```
disk(P(delta)-T_d(delta), e/2)
disk(P(tau)-T_d(delta), e).
```

The endpoint precision `tau` is independent of the leaf count. If `a>=B`,
the endpoint and sum are exactly zero.

### Damping-aware products and the actual frozen components

`complex-damped-product.lisp` compares against the actual reciprocal/phase
sampler `D(v,angle;nu,phi)`, whose disk radius is one. For a rational
complex argument `p`, rational `v>=0`, and independent positive precisions,
it proves

```
disk(E(p,beta)*D(v,angle;nu,phi)-E(p+(-v+i*angle),delta),
     beta+complexExpCap(p)*(nu+phi)+delta).
```

The coefficient of `beta` is one. The magnitude cap for the right argument
is absent from the final bound: it is absorbed in a computed auxiliary
precision, then eliminated by the rational disk-gap theorem. No analytic
limit or exact exponential is assumed in that elimination.

`mellin-clipped-exponential.lisp` applies this law to the actual zeroth
Mellin kernel and its independent primitive precisions. On a rational
interval contained in `[0,U]`, set

```
A = complexExpUniformCap(U)
B = beta+2*A*xi+delta.
```

Here `beta` is the fixed positive-exponential precision, `xi` is the
existing Mellin sampler's precision, and `delta` is an independent complex
exponential precision. Its three components are:

| Kind | Frozen signal factor | Complex rate | Moment cap |
|---|---|---|---|
| `3` | `1` | `-sigma-i*H` | `1` |
| `0` | `lowerExp(u,beta)` | `1-sigma-i*H` | `1` |
| `1` | `u*lowerExp(u,beta)` | `1-sigma-i*H` | `U` |

For `sigma>=0`, rational `H`, and every dyadic depth, the actual clipped
component `Q_kind` and the corresponding exponential grid `T_kind` satisfy

```
disk(Q_kind-T_kind, intervalLength*momentCap*B).
```

For kind `1`, the grid uses the inserted node as its first-moment weight;
`complex-exp-dyadic-moment-grid.lisp` constructs this grid. The displayed
bound is independent of depth and height. Grid-construction parameters
may still depend on height.

`mellin-clipped-endpoints.lisp` composes this comparison with the computed
endpoint formula for kinds `0` and `3`. For `sigma>1`, it computes clearance
`c=sigma-1` or `c=sigma`, respectively, and proves its squared-norm bound.
For requested additional error `e>0`, use

```
eta = e/(4*(1+intervalLength)*(1+c)).
```

The previous dyadic constructor, called with error `eta`, supplies the
depth, complex node precision and endpoint precision. Keeping `beta` and
`xi` fixed, the actual frozen component at that computed depth obeys

```
disk(actualComponentGrid-computedEndpointValue,
     intervalLength*(beta+2*A*xi)+e).
```

The two fixed source-precision errors are retained explicitly.

### Clipped first-moment endpoints and coupled budgets

`complex-exp-dyadic-moment-grid.lisp` now proves the weighted counterpart.
For interval `[A,b]` with `b=A+L`, cutpoint `a`, complex rate `z`, and
positive precision `delta`, let `v=max(A,a)` and `w=max(b,a)`. Define

```
Delta1(delta) = w*E(z*w,delta)-v*E(z*v,delta)
P1(delta) = (Delta1(delta)-P0(delta))/z,
```

where `P0` is the clipped zeroth endpoint above. The weighted grid `T1`
uses `(right-node)*node*E(z*node,delta)` on each active leaf, with
`node=max(left,a)`. With `h=halvedWidth(L,d)` and `N*h=L`, write

```
t = complexL1(z)
C = complexExpUniformCap(t*b)
Q = complexExpUniformCap(1)+2*C+2
B0 = C*t^2*h^2+Q*delta
B1 = b*B0+C*t*h^2.
```

For `t*h<=1` and squared-norm clearance `c>0`, the proved errors are

```
disk(Delta1(delta)-(T0(delta)+z*T1(delta)), N*B1)
disk(P1(delta)-T1(delta), N*(B1+B0/c)/c).
```

The zeroth quadrature error is included in the first-moment primitive
bound. Changes of endpoint precision cost at most
`2*(b+1/c)*(delta1+delta2)/c`. Empty clipped intervals give exactly zero.

`complex-exp-dyadic-moment-integral.lisp` computes the parameters from
requested error `e>0`. Put

```
M = b+1/c
G = C*(M*t^2+t)
V = M*Q
W = (t+G*L)*L
eta = min(1,c*e/4)
d = halvingDepth(W,eta,precisionFuel(W,eta))
tau = c*e/(16*(1+M))
delta = min(tau,c*e/(16*(1+N*V))).
```

It proves `t*h<=1`, `G*L*h<=c*e/4`, `N*V*delta<=c*e/16`, and the endpoint
precision budget. Consequently

```
disk(P1(delta)-T1(delta), e/2)
disk(P1(tau)-T1(delta), e).
```

For a fixed rate, interval and requested error, the computed mesh and
precisions are uniform in the cutpoint.
`mellin-clipped-moment-endpoints.lisp` applies this to the actual frozen
`u*lowerExp(u,beta)` component at `sigma>1`. With `c=sigma-1`, interval
length `L`, and containing log cap `U`, it requests additional error
`e/(4*(1+U*L)*(1+c))` from the weighted constructor and proves

```
disk(actualMomentGrid-computedMomentEndpoint,
     L*U*(beta+2*complexExpUniformCap(U)*xi)+e).
```

Thus all three frozen components have computed endpoint comparisons with
their source errors retained. The following construction assembles them
on a common mesh. Boundary removal and the computed-series comparison
are proved in the later sections.

### Common refinement and the full finite endpoint sum

`complex-exp-dyadic-refinement.lisp` and
`complex-exp-dyadic-moment-refinement.lisp` preserve these endpoint estimates
at every natural depth above the computed minimum. With the refined leaf
count `N`, the unweighted node precision becomes
`c*e/(16*(1+N*Q))`; the weighted precision becomes
`min(tau,c*e/(16*(1+N*V)))`. The endpoint precisions stay fixed. Mesh
monotonicity and `N*h=L` control the geometric terms; the new precision
controls the accumulated evaluation errors.

`mellin-clipped-refinement.lisp` transfers these results to the actual
components. `mellin-clipped-common-mesh.lisp` computes the maximum of their
three minimum depths and an optional additional minimum. The depth is
independent of the logarithmic cutpoint. All components use the same fixed
signal precision `beta` and kernel/phase sample precision `xi`; their
intermediate complex node precisions may differ.

Write `E_k(a)` for the computed component endpoint on `[A,A+L]` contained
in `[0,U]`, at requested component error `e>0`. With

```
B  = beta+2*complexExpUniformCap(U)*xi
R0 = L*B+e
R1 = L*U*B+e,
```

kinds `0` and `3` have radius `R0`, and kind `1` has radius `R1`.
For a rational index `n>1` and cutpoint at or above its
computed lower logarithm, the clipped ramp endpoint is
`E_0(a)/n-E_3(a)`, with radius `(1+1/n)*R0`.

`mellin-clipped-family-endpoints.lisp` applies this to every actual
Mangoldt weight and logarithmic cutpoint. For the frozen signal's
`N=N(U)`, primitive precision `beta=signalExponentialPrecision(U,m)`,
weights `w_n=lowerMangoldt(n,beta)`, cutpoints
`a_n=lowerLog(n,eta_n)` and `g=1+lowerEuler(beta)`, define

```
mass = sum(n=2..N, w_n*(1+1/n))
P    = sum(n=2..N, w_n*(E_0(a_n)/n-E_3(a_n)))
       -E_1(0)+g*E_0(0)
Rfamily = mass*R0+R1+abs(g)*R0.
```

The mass is rational and nonnegative. `mellin-frozen-endpoints.lisp`
proves that the full clipped linear quadrature differs from `P` by a
complex disk of radius `Rfamily`. At common mesh width `h`, restoring
the crossing cells and then the actual signal gives

```
disk(actualDyadicSum-P,
     L*K(U,1)*(xi+m)+h*K(U,1)*m+Rfamily).
```

Here `m>0` is the frozen signal's model error. The construction cap and
its coefficients remain fixed throughout both quadrature and refinement.

The same book compares the existing `lw-mellin-bounded-integral` at
integral precision parameter `q>0` with this endpoint expression on
`[0,U]`. It sets `xi=integralPrecision(U,q)` and includes the native
`integralDepth(U,sigma,H,q)` in the common depth. If their mesh widths are
`h_native` and `h`, the additional proved cross-depth radius is

```
Rcross = U*(spatialSlope(U,sigma,H,1)*(h_native+h)
           +spatialErrorFactor(U,1)*(xi+xi)).
```

`lw-mellin-bounded-endpoint-comparison` certifies the bounded constructor
minus `P` in the disk with radius
`Rcross+U*K(U,1)*(xi+m)+h*K(U,1)*m+Rfamily`.
These are explicit finite arithmetic comparisons for `sigma>1`.
The next budget chooses all internal tolerances, and transfers the
endpoint family to the actual improper evaluator.

### Total endpoint budgets and the improper family

`mellin-endpoint-budgets.lisp` proves a precision-independent mass bound
`mass<=N*(N+1)`, using `0<=w_n<=n`. It also proves
`beta<=m`, `abs(g)<=3`, `xi<=q/4` and `Rcross<=q`.
Define, for the construction cap `U>=0`,

```
M = N(U)*(N(U)+1)
F = M+U+4
X = complexExpUniformCap(U)
K = K(U,1)
J = 1+3*U*K+U*F*(1+2*X)+F.
```

All factors are computed rationals, with `F>=4` and `J>=1`. The cost
`J` depends on `U`; at fixed `U` it is independent of sigma, height,
target precision, primitive coefficient precision and common mesh depth.
For the diagonal choice `m=q=e=r>0`, ACL2 proves that the complete bounded
endpoint radius is at most `J*r`. Given total tolerance `eps>0`, set

```
r = endpointRequest(U,eps) = min(1,eps/(16*J)).
```

The request is positive, rational, at most 1, and satisfies
`r<=eps/16` and `J*r<=eps/16`. The computed bounded endpoint
`P(U,sigma,H,eps)` is the full frozen endpoint above with both its model
and component requests equal to `r`. Consequently, for `sigma>1`,

```
disk(boundedIntegral(U,sigma,H,0,r)-P(U,sigma,H,eps), eps/16).
```

`mellin-improper-endpoints.lisp` proves that these endpoint values are
rational complex pairs. For `sigma>2`, it defines

```
U = integralCutoff(sigma,0,eps)
Pstar(sigma,H,eps) = P(U,sigma,H,eps).
```

The actual improper evaluator is the bounded constructor on this same
interval at request `eps/2`. Its proved bounded Cauchy estimate costs
`eps/2+r` when changing the request to `r`; the new endpoint estimate
costs `eps/16`. Since `r<=eps/16`, the total is at most `eps`:

```
disk(integral(sigma,H,0,eps)-Pstar(sigma,H,eps), eps).
```

Combining this with the actual improper evaluator's Cauchy bound
`5*(eps1+eps2)` proves

```
disk(Pstar(sigma,H,eps1)-Pstar(sigma,H,eps2), 6*(eps1+eps2)).
```

This is an arithmetic Cauchy estimate across changing cutoffs, prime
truncations and frozen coefficients. The finite ray-endpoint normalization
below retains those frozen cutpoints. The later boundary-decay and
Mellin–Dirichlet series sections complete the arithmetic comparison.
The evaluated logarithmic-derivative connection is proved below;
analytic interpretation remains open.

### Frozen logarithms and finite Dirichlet normalization

`complex-log-ramp-independent.lisp` separates the logarithm precision
`eta` from the exponential precision `delta`. For `s=sigma+i*H`,
`sigma>1`, `c=sigma-1`, `n>1`, `a=lowerLog(n,eta)` and
`0<eta,delta<=1`, put `B_n=complexLogRampCap(sigma,H,n)`. It proves

```
disk(E((1-s)*a,delta)-n*E(-s*a,delta),
     (B_n+4)*delta+2*S(n)*eta).
```

The ray endpoint is

```
L_n = E((1-s)*a,delta)/(n*(s-1))-E(-s*a,delta)/s,
```

and differs from `D_n=E(-s*a,delta)/(s*(s-1))` by radius
`((B_n+4)*delta+2*S(n)*eta)/(n*c)`. The logarithmic cutpoint stays fixed
when the complex exponential is refined.

`complex-log-ramp-family.lisp` applies this to the actual lower Mangoldt
weights `w_n=lowerMangoldt(n,beta)` at any fixed positive coefficient
precision `beta`. For total truncation `N`, frozen model error `m>0`,
and `k<=N`, use the frozen family's existing parameters

```
q = m/(16*(1+N))
eta_n = min(1,q/S(n))
a_n = lowerLog(n,eta_n)
C_k = sum(n=2..k, B_n+4).
```

The bound `0<=w_n<=n` cancels the denominator `n` in each component
error. The family difference between `sum(w_n*L_n)` and `sum(w_n*D_n)`
has radius

```
(delta*C_k+2*max(k-1,0)*q)/c.
```

The normalized family factors exactly:

```
sum(n=2..k, w_n*D_n)
 = sum(n=2..k, w_n*E(-s*a_n,delta))/(s*(s-1)).
```

The cost `C_k` is independent of the frozen logarithm and coefficient
precisions. Given requested exponential error `e>0`, the book computes

```
delta = min(1,c*e/(16*(1+C_k))).
```

It is positive and at most 1. The theorem
`lw-complex-log-ramp-family-computed-normalization` bounds the complete
weighted normalization error by `e/16+m/(8*c)`. This includes the
existing frozen logarithm budget rather than replacing its cutpoints.
### Exact upper boundaries for the finite primitive family

`complex-exp-boundaries.lisp` defines

```
B0(z,x,delta) = -E(z*x,delta)/z
B1(z,x,delta) = x*B0(z,x,delta)-B0(z,x,delta)/z.
```

The zeroth primitive on `[a,b]` is exactly `B0(z,a)-B0(z,b)`; the
first-moment primitive is exactly `B1(z,a)-B1(z,b)`. The clipped versions
use `max(start,cutpoint)` and `max(end,cutpoint)`, so the identities also
cover cutpoints beyond the interval. For a damped rate
`z=-(r+i*H)`, `r>0`, and `R=1/(r+i*H)`, the normalized boundaries are

```
B0(z,x,delta) = E(z*x,delta)*R
B1(z,x,delta) = E(z*x,delta)*(x*R+R^2).
```

Their values at zero are exactly `R` and `R^2`.

`mellin-dirichlet-boundaries.lisp` uses the frozen coefficients and
cutpoints constructed at `U`, but allows an independent integration
endpoint `T>=0`. Let `s=sigma+i*H`, `z1=1-s`, `z3=-s`,
`v_n=max(T,a_n)`, and retain one common node precision `delta>0`.
For the clipped ramp primitive `P_n(T)`, define its upper boundary

```
V_n(T) = B0(z1,v_n,delta)/n-B0(z3,v_n,delta).
```

The exact identity is `P_n(T)+V_n(T)=L_n`, with `L_n` the ray endpoint
above. It passes through the complete Mangoldt-weighted finite sum. If
`g=1+lowerEuler(beta)`, the full primitive and boundary are

```
P(T) = sum(w_n*P_n(T))-P1(z1;0,T,0,delta)
       +g*P0(z1;0,T,0,delta)
V(T) = sum(w_n*V_n(T))-B1(z1,T,delta)+g*B0(z1,T,delta).
```

The reciprocal terms from the origin give the full normalized model

```
D = sum(w_n*E(-s*a_n,delta))/(s*(s-1))
    -1/(s-1)^2+g/(s-1).
```

At `delta=complexLogRampFamilyPrecision(sigma,H,N(U),e)`, ACL2 proves

```
disk(P(T)+V(T)-D, e/16+m/(8*(sigma-1))).
```

This formula includes both correction terms and retains the frozen
logarithm error. The following precision transfer composes it with the
existing Mellin endpoint constructor and the actual evaluators.

### Common endpoint precision and actual Dirichlet comparison

`mellin-endpoint-precision.lisp` records the existing zeroth endpoint
precisions `tau_0,tau_3` and first-moment precision `tau_1`. They are
the precisions in the endpoint values above, at component error `r>0`.
The proved primitive Cauchy bounds give radius at most `r/16` when
changing each endpoint to any positive `delta<=tau_k`. Summing the ramps
with the actual weights and adding both corrections gives

```
G(U,m) = mass(N(U),beta)+1+abs(1+lowerEuler(beta))
beta = signalExponentialPrecision(U,m)
disk(frozenEndpoint(U,0,T,sigma,H,m,r)-P(T,delta), G(U,m)*r/16).
```

The factor is rational and satisfies `1<=G(U,m)<=F(U)<=J(U)`, where
`F,J` are the precision-independent interval factors above. The
construction cap `U` and integration endpoint `T` remain independent.

The common precision is computed as

```
delta = min(tau_0,tau_3,tau_1,
            complexLogRampFamilyPrecision(sigma,H,N(U),e)).
```

It is positive, rational, and at most 1. The normalization radius
`e/16+m/(8*(sigma-1))` remains valid at any finer positive precision
than the family's original computed precision.

`mellin-dirichlet-comparison.lisp` sets `T=U` and uses the existing
`r=endpointRequest(U,e)` for the model, bounded integral and component
requests. Its common precision is
`dirichletNodePrecision(U,sigma,H,e)`. With all endpoint and boundary
values evaluated at that precision, the three comparison radii are

```
actual bounded integral -> frozen endpoint: e/16
frozen endpoint -> common-precision primitive: e/256
primitive + boundary -> finite Dirichlet model:
    e/16+r/(8*(sigma-1)).
```

For `sigma>2`, their sum is at most `e/4`. Thus the actual bounded
constructor satisfies

```
disk(boundedIntegral(U,sigma,H,0,r)
     +computedDirichletBoundary(U,sigma,H,e)
     -computedDirichletModel(U,sigma,H,e), e/4).
```

For the default improper evaluator, take
`U=integralCutoff(sigma,0,e)`. Its bounded request is `e/2`; changing it
to `r` costs at most `e/2+r`. Since `r<=e/16`, the theorem
`lw-mellin-improper-dirichlet-comparison` proves

```
disk(integral(sigma,H,0,e)
     +computedDirichletBoundary(U,sigma,H,e)
     -computedDirichletModel(U,sigma,H,e), e).
```

Every request, cutoff and precision in this comparison is computed.
The boundary is now bounded and removed by the computed decay argument
below. The series and evaluated logarithmic-derivative comparisons are
proved later for `sigma>3`; analytic interpretation remains open.
The truncation uses `signalCount(X)=nfix(abs(numerator(X)))` at the
rational spatial cap `X`. The certified frozen-family tail is independent
of that finite count and supplies the available uniform cutoff control.

### Independently refined frozen-family tails

The books `signal-exponential-refinement.lisp` and `mellin-refined-*.lisp`
separate the point-exponential precision from the fixed construction data.
For construction cap `U>=0` and model request `0<m<=1`, keep
`N=N(U)`, coefficient precision `beta=signalExponentialPrecision(U,m)`,
and every logarithmic cutpoint fixed. At any `u>=0`, choose any rational
`0<eta<=beta`. The new signal family uses `lowerExp(u,eta)` in the old
finite linear expression and satisfies

```
abs(refinedSignal(U,u,m,eta)) <= 5*lowerExp(u,eta)^2.
```

There is no `u<=U` premise. Native precision `eta=beta` recovers the
existing frozen sampler exactly. The kernel-shift identity gives a
mass-five tail majorant. Its dyadic potential on `[S,T]` is

```
10*tailCoefficient(sigma-2,j,1)*(1/S-1/T),
```

provided `sigma>2`, `S>0`, `j+2<=(sigma-2)*S`, and the dyadic
mesh is at most `S`. At the existing mass-four improper cutoff
`S=integralCutoff(sigma,j,c)`, its radius is at most `5*c/4`.
This explicitly accounts for the different majorant masses.

For `j=0`, exact finite linearity, the weighted crossing estimate and the
component endpoint comparisons transfer this refined tail to the complete
endpoint family. The interval cap `T` is independent of `U`. Both
corrections, the Mangoldt weights and the logarithmic cutpoints are retained.

The comparison budget is computed after `T` is chosen. Write
`L=T-S`, `M=primeEndpointMass(N,beta)`,
`g=abs(1+lowerEuler(beta))`, `K=kernelSpatialCap(T,1)`, and
`A=complexExpUniformCap(T)`. The exact rational cost and request are

```
W = 1 + K*m + L*(M+T+g)*(1+2*A) + M+1+g
r = min(1,beta,e/(16*W)).
```

The source exponential and kernel precisions are `r`; coefficients
and cutpoints keep their original precisions. A computed halving depth
makes the mesh at most `min(S,r)`. The common component depth is at
least that depth, so the complete crossing and endpoint comparison error
is at most `e/16`. The resulting theorem
`lw-mellin-computed-refined-endpoint-at-integral-cutoff` proves, for
`S=integralCutoff(sigma,0,c)` and every rational `T>=S`,

```
disk(computedRefinedEndpoint(U,T,S,T-S,sigma,H,m,e), 5*c/4+e/16).
```

All requests and depths are computed; there is no convergence assumption.

### Common-precision boundary tails

`mellin-interval-precision.lisp` computes one finer node precision for
all endpoints on `[S,T]`. The first-moment precision retains `S` in its
amplification factor. In `mellin-interval-boundaries.lisp`, the full
interval primitive satisfies the exact identity

```
P_interval(U,S,T-S,sigma,H,m,delta) = V(U,S,delta)-V(U,T,delta),
```

where `V` is the existing finite boundary with the same fixed construction
data. Transferring the endpoint family to this primitive costs at most
`G(U,m)*r/16`. The refined comparison cost `W` above dominates `G`,
so its computed request makes that transfer cost at most `e/256`.

`lw-mellin-common-node-boundary-at-integral-cutoff` composes the tail
and transfer bounds. For `S=integralCutoff(sigma,0,c)`, `sigma>2`,
`0<m<=1`, and every rational `T>=S`, a computed positive node threshold
`d` gives, at every rational `0<delta<=d`,

```
disk(V(U,S,delta)-V(U,T,delta), 5*c/4+e/8).
```

`mellin-boundary-precision.lisp` proves Cauchy bounds for the boundary
components by cancelling their precision-independent values at zero in the
primitive Cauchy bounds. With `r0=endpointRequest(U,e)` and the original
`d0=dirichletNodePrecision(U,sigma,H,e)`, it proves, for `sigma>1` and
every rational `0<delta<=d0`,

```
disk(computedDirichletBoundary(U,sigma,H,e)
     -V(U,U,sigma,H,r0,delta), e/256).
```

### Computed boundary decay and its removal

`complex-boundary-decay.lisp` proves, for real rate `r>1`, rational
`T>=1` and positive node precision `delta`, that both `B0` and `B1`
have radius

```
K(T,delta) = 8/T+2*(T+1)*delta.
```

The quadratic damped-exponential estimate supplies the decay; coarse
clearance one bounds the reciprocal rate independently of height.
In `mellin-far-boundary.lisp`, choosing `T>=N(U)` puts it beyond every
frozen cutpoint, since `lowerLog(n)<=n-1`. Summing with the actual
weights and both corrections gives radius `G(U,m)*K(T,delta)`.

For any requested far-boundary error `a>0` and starting point `S>=0`,
the constructors are

```
T = 1+S+N(U)+precisionFuel(16*G(U,m),a)
d_far = a/(4*G(U,m)*(1+T)).
```

They are rational, `T>=max(1,S,N(U))`, and `d_far>0`.
At every rational `0<delta<=d_far`, the complete finite boundary at
`T` has radius at most `a`. General boundary rationality is also proved.

`mellin-dirichlet-decay.lisp` sets `U=integralCutoff(sigma,0,e)`,
`m=endpointRequest(U,e)`, `S=U` and `a=e/4`. It computes a common
node precision below the original one, the interval-tail threshold and
`d_far`. Near-boundary stability, the interval difference and the far
boundary consume respectively

```
e/256, 5*e/4+e/32, e/4.
```

Their sum is `393*e/256<2e`. The theorem
`lw-mellin-computed-dirichlet-boundary-decay` therefore proves

```
disk(computedDirichletBoundary(U,sigma,H,e), 2*e).
```

Removing this boundary from the preceding improper comparison gives
`lw-mellin-improper-dirichlet-without-boundary`, for `sigma>2`,

```
disk(integral(sigma,H,0,e)-computedDirichletModel(U,sigma,H,e), 3*e).
```

Every auxiliary endpoint and precision is computed, and no limit argument
or convergence hypothesis is used. The following series construction
and comparison complete the arithmetic identity in `sigma>3`.
The evaluated logarithmic-derivative connection is proved below;
analytic interpretation and general model generation remain open.

### Finite Dirichlet precision and computed values

`complex-damped-continuity.lisp` proves spatial transport uniformly in
the closed negative half-plane. For a nonnegative real rate `sigma` and
nonnegative logarithmic arguments `u,v`, its Laplace specialization has
radius

```
2*(sigma+abs(H))*abs(u-v)+32*(d_left+d_right).
```

The base arguments do not enter the constant. Small increments use the
damped product law and a unit-scale exponential bound; larger increments
use the damped unit caps. Every auxiliary precision is computed.

`dirichlet-term-transport.lisp` applies this to changing lower logarithms
and proves the corresponding Mangoldt precision bound. Let
`C=2*(sigma+abs(H))`, and give each side its own truncation budget
`N_i`, model error `m_i`, coefficient error `b_i` and node error `d_i`.
The frozen logarithm request for term `n` is

```
q_i = m_i/(16*(1+N_i))
eta_i(n) = min(1,q_i/expLipschitzCap(n)).
```

The actual lower Mangoldt weight is at most `n`, while
`n<=expLipschitzCap(n)`. Thus each weighted logarithm error is at most
`q_i`. For `sigma>1`, a common prefix `k<=N_left,N_right` and
positive node errors at most 1, `dirichlet-family-precision.lisp` proves

```
disk(P_left(k)-P_right(k),
     C*(m_left+m_right)/16
     +16*k*(k+1)*(d_left+d_right)
     +2*k*(b_left+b_right)).
```

Here `P_i` is the existing `lw-complex-dirichlet-prime-sum` using
that side's fixed total `N_i`. The logarithm contribution is independent
of the common-prefix count.

For requested finite-sum error `e>0` at fixed count `k`, the new
constructor computes

```
m = min(1,e/(1+C))
b = e/(8*(1+k))
d = min(1,e/(64*(1+k*(k+1)))).
```

It evaluates `P(k,k,m,b,d)`. The value is rational-complex and its
precision Cauchy radius is `e1+e2`. The existing prime-sum evaluator,
at arbitrary positive `m,b,d` and any total `N>=k`, also has the
explicit comparison

```
disk(P(k,N,m,b,d)-finiteValue(k,e),
     C*m/16+16*k*(k+1)*d+2*k*b+e).
```

### Dirichlet tails and a computed series value

The following results use `sigma>3`, a right half-plane containing the
Landau anchor. They do not extend the identity into the zero region.

Write `E_r(n,eta,d)` for the existing logarithmic-ramp exponential
at rate `r`, height `H`, lower-logarithm request `eta` and node request
`d`. The certified rate shift is

```
disk(E_(r-1)-n*E_r, (cap(r,H,n)+4)*d+2*S(n)*eta),
S(n)=expLipschitzCap(n).
```

For `0<eta,d<=1`, applying it at `sigma,sigma-1,sigma-2` starts from
the damped cap `disk(E_(sigma-3),2)`.
`dirichlet-cubic-decay.lisp` recovers each preceding exponential by
division by `n`. For any rational `0<=w<=n`, it proves

```
D(n) = cap(sigma,H,n)+cap(sigma-1,H,n)+cap(sigma-2,H,n)+12
disk(w*E_sigma(n,eta,d), 2/n^2+D(n)*d+6*S(n)*eta).
```

The actual lower Mangoldt weight satisfies that range check. With
`eta(n)=smoothedRampLogError(n,total,m)` and
`q=smoothedRampUnitError(total,m)=m/(16*(1+total))`, the last error is
at most `6*q`.

`dirichlet-tails.lisp` computes `D_N=sum_(n=2..N) D(n)` and proves
its rationality and nonnegativity. For `1<=M<=N`, the difference of
the existing raw prime sums, at the same `total,m,b,d`, has radius

```
2*(1/M-1/N)+(D_N-D_M)*d+6*(N-M)*q.
```

The reciprocal part telescopes using
`2/n^2<=2*(1/(n-1)-1/n)`. If also `N<=total`, the radius is at most

```
2/M+D_N*d+3*m/8.
```

No infinite-tail premise is supplied. All coefficients remain the actual
computed lower Mangoldt values.

For auxiliary request `a>0`, `dirichlet-finite-cauchy.lisp` keeps
the preceding model and coefficient precision formulas at total `N`
and chooses the finer node precision

```
d = min(1,a/(64*(1+N*(N+1)+D_N))).
```

This controls both the finite comparison error and the tail rounding
cost. Compare the two canonical finite values to this one auxiliary
family, then use its finite tail. With `a=e1+e2`, the exported theorem is

```
disk(finiteValue(N,e1)-finiteValue(M,e2), 2/M+4*(e1+e2)),
1<=M<=N.
```

Finally, `dirichlet-series.lisp` defines

```
seriesCount(e) = 1+precisionFuel(8,e)
seriesValue(sigma,H,e) = finiteValue(seriesCount(e),e/32).
```

The count is a positive integer with `2/seriesCount(e)<=e/4`.
The value is rational-complex and satisfies

```
disk(seriesValue(sigma,H,e1)-seriesValue(sigma,H,e2), e1+e2).
```

The proof considers both possible count orderings; it assumes no
monotonicity of `precisionFuel` in its error argument. For every
`N>=seriesCount(e)` and finite request `f>0`, it also proves

```
disk(finiteValue(N,f)-seriesValue(sigma,H,e), 3*e/8+4*f).
```

These are arithmetic convergence bounds for the computed Mangoldt
Dirichlet family. The next section identifies its normalized value with
the actual improper Mellin evaluator.

### Mellin–Dirichlet series identity as Cauchy names

For `sigma>3`, `mellin-series-precision.lisp` bounds the errors in
the existing finite Mellin model independently of its truncation count.
Let `N=rampCount(U)`, `C_N=logRampFamilyCost(sigma,H,N)` and let
`d` be that model's node precision. The certified bounds include

```
N*(N+1) <= 2*(1+C_N)
(1+C_N)*familyPrecision(sigma,H,N,e) <= (sigma-1)*e/16
16*N*(N+1)*d <= 2*(sigma-1)*e.
```

The coefficient request `b` obeys `2*N*b<=m`, where the internal
model request has `m<=e/16`. With

```
K = 1+4*sigma+2*abs(H),
```

the raw prime sum used by the Mellin model differs from the canonical
`finiteValue(N,f)` by at most `K*e+f`. The constant contains no
truncation count or construction cap. Also `rampCount(U)>=U` and
`rampCount(U)>=3`.

`dirichlet-transform.lisp` defines the normalized series name, with
`s=sigma+i*H`,

```
A(e) = seriesValue(sigma,H,e/4)/(s*(s-1))
       -1/(s-1)^2 + (1+lowerEuler(e/4))/(s-1).
```

Both reciprocal factors have disk cap 1 in this half-plane. Transport
through the normalization therefore costs at most the prime-sum error
plus the Euler-value error. The computed value is rational-complex and
has Cauchy radius `e1+e2`.

`mellin-dirichlet-series.lisp` aligns this name with the existing
improper Mellin evaluator using the explicit auxiliary request

```
J = seriesCount(e/4)
T = mellinTailCoefficient(sigma-2,0,4)
tau = min(e/(16*(K+10)), 2*T/(1+J))
U = integralCutoff(sigma,0,tau).
```

Here `T>0`, `tau>0`, and the constructor proves

```
(K+9)*tau <= e/16
J <= rampCount(U).
```

The second inequality follows from the existing cutoff bound
`2*T<=tau*U` and `rampCount(U)>=U`; no monotonicity of the
series count is assumed. Comparing at finite request `f=e/64`
gives prime-sum error `K*tau+11*e/64`. The Euler correction adds
at most `tau/16+e/4`, so the full finite Mellin model differs from
`A(e)` by at most `(K+1)*tau+27*e/64`.

The existing improper Mellin comparison costs `3*tau`, and changing
its request from `e1` to `tau` costs `5*(e1+tau)`. Their sum is
bounded by `5*e1+e2` when `tau` uses `e=e2`. The exported theorem
`lw-mellin-dirichlet-series-comparison` is therefore

```
disk(integral(sigma,H,0,e1)-A(e2), 5*e1+e2).
```

This is an arithmetic identity of the two Cauchy names, proved for
arbitrary positive rational requests with every auxiliary parameter
computed. The evaluated logarithmic-derivative identity is proved below.
Continuation of model comparisons into the zero region and compatible
uniform constants remain required for the full reduction.

### Logarithm and complex-power multiplication

`log-multiplication.lisp` proves logarithm multiplicativity from the
existing rational rectangle partitions. Scaling every endpoint and the
start by a positive rational factor preserves both the lower and upper
partition sums exactly. Append the partition from 1 to `a` to the
scaled partition from `a` to `a*b`, then compare it with the native
product partition.

For rational `a,b>1` and independent positive requests `ea,eb,ep`,
the product enclosure overlaps the sum enclosure:

```
lowerLog(a*b,ep) <= upperLog(a,ea)+upperLog(b,eb)
lowerLog(a,ea)+lowerLog(b,eb) <= upperLog(a*b,ep).
```

The existing width bounds then prove

```
abs(lowerLog(a,ea)+lowerLog(b,eb)-lowerLog(a*b,ep)) <= ea+eb+ep.
```

This uses finite partition identities and comparisons; no classical
logarithm identity is supplied as an input.

`dirichlet-product.lisp` transfers the result to the existing
logarithmic-ramp exponentials. Write `E(n,eta,d)` for
`lw-complex-log-ramp-independent-exp(sigma,H,n,eta,d)`, and define

```
B(n) = complexExpUniformCap((sigma+abs(H))*n)
C = 2*(sigma+abs(H)).
```

For rational `sigma>=0`, height `H`, `a,b>1` and six independent
positive logarithm/node requests, the exported multiplication bound is

```
disk(E(a,eta_a,d_a)*E(b,eta_b,d_b)-E(a*b,eta_p,d_p),
     B(b)*d_a+B(a)*d_b+C*(eta_a+eta_b+eta_p)+66*d_p).
```

The exponential product law first compares with the value at the sum of
the two computed logarithms. Its error is
`B(b)*d_a+B(a)*d_b+2*d_p`. Damped spatial transport compares that
sum with the computed product logarithm at cost
`C*(eta_a+eta_b+eta_p)+64*d_p`. The caps depend on the factors,
rate and height; they are independent of the precision requests.

For any rational `e>0`, the constructor computes

```
p = e/(1+B(a)+B(b)+66+3*C).
```

Using `eta_a=eta_b=eta_p=d_a=d_b=d_p=p` makes the product error at
most `e`. Every cap and precision is rational and its validity is
proved. These are evaluator identities needed for the finite Dirichlet
convolution. The following construction supplies the ordinary and
logarithm-weighted series. The finite divisor identity is proved below;
the finite hyperbolic convolution and native series product are also
proved below. Derivative interpretation and continuation remain open.

### Ordinary and logarithm-weighted zeta series

The five `zeta-*` series books construct a separate Dirichlet family
with explicit coefficients. For `n>=2`,

```
w(false,n,b) = 1
w(true,n,b) = lowerLog(n,b).
```

`zeta-term-transport.lisp` proves `0<=w<=n` and coefficient
precision error at most `b1+b2`. The same weighted logarithm budget
`w*eta(n,total,m)<=m/(16*(1+total))` therefore applies. Its term
transport bound retains independent totals and all three precision kinds.

`zeta-family-precision.lisp` defines the raw partial sum
`Q(mode,N,total,m,b,d)`. Count 0 is the empty sum; the `n=1`
term is exactly 1 in ordinary mode and 0 in logarithm mode. Higher terms
are `w(mode,n,b)*E(n,eta(n,total,m),d)`, using the existing computed
complex powers. The definition contains no Mangoldt coefficients.

The finite constructor uses the existing model, coefficient and node
precision budgets. Its value is rational-complex, with fixed-count
Cauchy radius `e1+e2`. A common prefix `k<=N1,N2` has the same
uniform precision comparison as the Mangoldt family. For arbitrary
positive requests and any `total>=k`,

```
disk(Q(mode,k,total,m,b,d)-zetaFinite(mode,k,e),
     2*(sigma+abs(H))*m/16+16*k*(k+1)*d+2*k*b+e).
```

`zeta-tails.lisp` specializes the generic weighted cubic bound to
these coefficients and reuses the computed cubic cost `D_N`. For
`1<=M<=N<=total` and `0<d<=1`, the raw finite tail has radius

```
2/M+D_N*d+3*m/8.
```

Using the existing finer tail-node request, `zeta-finite-cauchy.lisp`
then proves

```
disk(zetaFinite(mode,N,e1)-zetaFinite(mode,M,e2),
     2/M+4*(e1+e2)).
```

Finally, `zeta-series.lisp` computes

```
zetaSeries(mode,sigma,H,e)
  = zetaFinite(mode,seriesCount(e),e/32).
```

For `sigma>3`, it is rational-complex and has Cauchy radius
`e1+e2`. Every longer approximation, `N>=seriesCount(e)`, satisfies

```
disk(zetaFinite(mode,N,f)-zetaSeries(mode,sigma,H,e),3*e/8+4*f).
```

The proof handles either ordering of two computed cutoffs. These
constructors supply the ordinary and logarithm-weighted Dirichlet
series. The next section establishes a right-plane nonzero clearance
and a computable quotient. The finite divisor identity is proved below;
the finite hyperbolic convolution and native series product are also
proved below. Derivative interpretation and continuation to the zero
region remain required.

### Right-plane nonzero clearance and the series quotient

`zeta-series-clearance.lisp` sharpens the generic cubic bound for
an unweighted term. Use the existing weighted theorem at weight `n`,
then divide by `n`. For `sigma>3`, `n>1` and positive
logarithm/node requests at most 1,

```
disk(E(n,eta,d),2/n^3+D(n)*d+6*S(n)*eta).
```

The summable majorant satisfies

```
2/n^3 <= (1/2)*(1/(n-1)-1/n).
```

This follows from `4*(n-1)<=n^2`, or `(n-2)^2>=0`.
Summing from 2 through `N` gives potential `(1/2)*(1-1/N)`.
For the ordinary raw partial sum, `1<=N<=total`,

```
disk(Q(false,N,total,m,b,d)-1,1/2+D_N*d+3*m/8).
```

The shared finer node budget bounds the two rounding terms by an
auxiliary request `a`. Comparing with the canonical finite value
costs at most `a+e`. Taking `a=e` proves

```
disk(zetaFinite(false,N,e)-1,1/2+3*e)
disk(zetaFinite(true,N,e),2+3*e).
```

For the computed series at `sigma>3`, these imply

```
disk(zetaSeries(false,e)-1,1/2+e).
```

When `0<e<=1/4`, the ordinary series has real part at least
`1/4`, squared norm at least `1/16`, and reciprocal disk cap 4.
The logarithm-weighted series has disk cap 3 at the same requests.
These are proved bounds on the actual rational constructors.

`zeta-log-quotient.lisp` uses the explicit precision

```
p(e) = min(1/4,e/104)
R(e) = zetaSeries(true,p(e))/zetaSeries(false,p(e)).
```

The denominator clearance makes division valid. The existing quotient
difference theorem costs at most `4*(p1+p2)+48*(p1+p2)`, controlled
by the computed precision. Thus `R(e)` is rational-complex and has
Cauchy radius `e1+e2`. At its own finite precision it also satisfies

```
R(e)*zetaSeries(false,p(e)) = zetaSeries(true,p(e)).
```

This exact product identity concerns the explicit ratio and its
numerator. Its equality as a Cauchy name with the Mangoldt series is
proved below, using finite divisors, hyperbolic tails and native precision
comparison. Derivative interpretation and continuation needed for the
full Landau reduction remain open.

### Finite Mangoldt divisor identity

The nine books from `integer-divisibility.lisp` through
`mangoldt-divisor-log.lisp` construct the required integer arithmetic.
`lw-divides(d,n)` means that `d` is a positive integer, `n` is an
integer, and `n/d` is an integer. Its equivalence to the original MOD
tests is proved. A terminating subtractive Euclidean algorithm computes
`g,a,b` with `g=a*x+b*y` and `g|x,y`; these facts prove Euclid's
lemma for the existing `lw-primep` predicate.

Bounded least-divisor search then computes a prime divisor. Repeated
division terminates at a strictly smaller positive integer and constructs
`lw-prime-factors(n)`, a prime list whose product is `n`. A prime's
computed multiplicity `v_p(n)` satisfies, for positive integer `n`
and natural `k`,

```
lw-divides(p^k,n) <=> k <= v_p(n).
```

Each factor occurrence produces `p^(1+count(p,remainingFactors))`.
Thus repeated occurrences generate `p^v,...,p` exactly once. The resulting
`lw-prime-power-divisors(n)` has no duplicates, and its membership theorem
is exactly

```
d in primePowerDivisors(n)
  <=> posp(d) and primePowerData(d) and lw-divides(d,n).
```

All members lie between 1 and `n`. A bounded-scan reindexing proves
`lw-mangoldt-divisor-factor-sum`: for positive rational `e`,

```
D(n,e) = sum_{1 <= d <= n, d|n} lowerMangoldt(d,e)
       = sum_{p in primeFactors(n)} lowerLog(p,e).
```

The first sum is the actual recursive trial-divisor sum; the second
counts repeated prime factors. Both use the existing evaluators.
Logarithm multiplication and independent-precision Cauchy bounds give
`lw-mangoldt-divisor-log-error`. With `L=len(primeFactors(n))` and
positive rational `eta`,

```
abs(D(n,e)-lowerLog(n,eta)) <= 3*L*e + eta.
```

The constructor `lw-mangoldt-divisor-precision(n,E)` returns
`p=E/(2*(1+3*L))`. For every positive rational target `E`,
`lw-mangoldt-divisor-log-computed-error` proves

```
abs(D(n,p)-lowerLog(n,E/2)) <= E.
```

No factorization, primality oracle or logarithm identity is supplied as
a hypothesis. This proves the finite arithmetic divisor identity with
explicit rounding errors. The finite Dirichlet products are reindexed
below. The subsequent native precision comparison identifies the
Mangoldt series with the zeta-series ratio.

### Finite Dirichlet convolution with computed precision

`finite-dirichlet-convolution.lisp` proves the finite hyperbola identity
for arbitrary rational coefficient tables and rational complex-node
tables. It preserves independent factor cutoffs `A,B` and product
cutoff `N`: a divisor `a|n` contributes precisely when `a<=A` and
`n/a<=B`. Positive integer quotients and their bounds are proved from
`lw-divides`; no enumeration bijection is supplied as an input.
When `A=B=N`, the inner sum contains every positive divisor of `n`.

`mangoldt-dirichlet-convolution.lisp` constructs the tables from the
existing Mangoldt and complex-power evaluators and proves every lookup.
The sample at 1 is exactly `(1,0)`; for `n>1` the sample is
`lw-complex-log-ramp-independent-exp`. Thus the concrete hyperbola is

```
sum_{a*b<=N} lowerMangoldt(a,e) * E(a*b).
```

Exact reindexing gives its divisor-weighted form. The finite divisor
logarithm error and the proved sample cap 2 then bound its difference
from the logarithm-weighted finite sum by `2*C_N*e`, where

```
C_N = sum_{n=2..N} (1 + 3*len(primeFactors(n))).
```

`dirichlet-hyperbola-product.lisp` replaces each product node by the
actual product of samples. For rational `sigma>=0`, rational height
`H`, and positive integers `a,b`, set

```
Q(a,b) = 0                                  if a=1 or b=1,
         B(a)+B(b)+66+6*(sigma+abs(H))        otherwise,
P_N = sum_{a*b<=N} a*Q(a,b).
```

Here `B` is the previously computed Dirichlet product cap. At shared
logarithm and node precision `p>0`, the product-sample discrepancy has
radius `Q(a,b)*p`. The proved inequality
`0<=lowerMangoldt(a,e)<=a` bounds the weighted hyperbola error by
`P_N*p`, independently of the coefficient request `e>0`.

For any positive rational target `E`, the constructor
`lw-dirichlet-convolution-precision(sigma,H,N,E)` computes

```
p = min(1, E/(1+P_N+2*C_N)).
```

All costs are rational and nonnegative, and `0<p<=1`.
Using this same `p` for the Mangoldt coefficient, logarithm coefficient,
node logarithm and node rounding requests, the theorem
`lw-complex-mangoldt-finite-convolution` proves

```
disk(
  sum_{a*b<=N} lowerMangoldt(a,p)*E_p(a)*E_p(b)
  - sum_{n=2..N} lowerLog(n,p)*E_p(n),
  E).
```

Both sums are computed, and all table contents and precisions are
constructed. The first sum retains the hyperbolic cutoff `a*b<=N`.
The omitted pairs are bounded in the next section. The subsequent native
precision comparison proves the series product identity and ratio
agreement. Derivative interpretation and continuation remain required.

### Absolute hyperbolic tails and complete-prefix products

`hyperbola-majorants.lisp` proves finite reciprocal-square prefix and
tail bounds without a convergence hypothesis:

```
sum_{a=1..A} 1/a^2 <= 2,
sum_{M<a<=A} 1/a^2 <= 1/M.
```

For positive integer `M` and natural `N>=M^2`, a pair with `a*b>N`
has `a>M` or `b>M`. Summing the two rectangular majorants proves
`lw-hyperbola-tail-majorant-bound`, uniformly in natural `A,B`:

```
sum_{a<=A,b<=B,a*b>N} 4/(a^2*b^2) <= 16/M.
```

`dirichlet-hyperbola-tail.lisp` applies this bound to the actual
computed samples for rational `sigma>3`. At shared logarithm/node
precision `0<q<=1`, both the sample and its Mangoldt-weighted version
have radius at most

```
2/n^2 + D(n)*q,
D(1)=0,
D(n)=cubicNodeCost(sigma,H,n)+6*expLipschitzCap(n)  for n>1.
```

The coefficient request may be any positive rational value. This follows
from the proved bound `0<=lowerMangoldt(n,e)<=n` and the existing cubic
decay theorem. Multiplication and `q^2<=q` give the pair radius

```
4/(a^2*b^2) + R(a,b)*q,
R(a,b)=2*D(a)+2*D(b)+D(a)*D(b).
```

Let `R_ABN` be the computed sum of `R(a,b)` over omitted pairs.
The theorem `lw-dirichlet-hyperbola-absolute-tail` proves that the
actual omitted-pair sum lies in the disk of radius

```
16/M + R_ABN*q.
```

The same book proves the exact identity splitting the product of two
complete finite prefixes into its hyperbola and its omitted-pair sum.
No discarded part is hidden in a comparison premise.

For target `E>0`, the final constructor chooses

```
M = dirichletSeriesCount(E/4),
N = M^2,
R = R_NNN,
b = E/(2*(1+R)),
p = dirichletConvolutionPrecision(sigma,H,N,b).
```

The existing count bound gives `16/M<=E/2`. The new precision bound
proves `0<p<=min(1,b)`, so the rounding and finite convolution costs
satisfy `R*p+b<=E/2`. Consequently
`lw-complex-dirichlet-computed-rectangle-convolution` proves

```
disk(
 (sum_{a=1..N} lowerMangoldt(a,p)*E_p(a))
 *(sum_{b=1..N} E_p(b))
 - sum_{n=2..N} lowerLog(n,p)*E_p(n),
 E).
```

All three prefixes use the constructed common precision and the
existing sample evaluator. This is a product of complete finite
prefixes. The next section compares these common-precision prefixes
with the native series' varying precisions and proves the infinite
product identity and agreement with the zeta-series ratio.

### Native series product and ratio agreement

`dirichlet-common-precision.lisp` uses one coefficient interface for
Mangoldt, logarithm and ordinary weights. For natural `n>1`, every
coefficient is rational, lies between 0 and `n`, and has independent
precision error at most `e1+e2`. All three common-precision prefixes
are identified with the existing sample constructors.

Write `S=2*(sigma+abs(H))` and define the computed finite cost

```
K_N = sum_{n=2..N} (n*(S+32)+2).
```

Each native logarithm, coefficient and node request is bounded above
by its parent finite request `d`. Termwise transport therefore proves
that a prefix at common precision `q>0` differs from the actual native
finite evaluator at request `d>0` by at most `K_N*(q+d)`.
For `N>=dirichletSeriesCount(e)`, composition with the existing
series comparison gives radius

```
K_N*(q+d) + 3*e/8 + 4*d.
```

For target `E>0`, the constructor
`lw-dirichlet-native-refinement(sigma,H,N,E)=E/(5+2*K_N)` is positive.
Any `0<q<=d` at this computed `d` gives radius `3*e/8+E`
against the native series value. This proves the comparison for all
three families, including their exact `n=1` cases.

`dirichlet-series-product.lisp` takes the maximum of the required
native cutoffs and the computed square cutoff. It chooses a shared
request satisfying both the rectangle and native refinement budgets.
The resulting slack is removed by the existing rational disk-gap
constructor; no analytic limit premise is added.

Let `M(e)`, `Z_0(e)` and `Z_log(e)` be the actual native Mangoldt,
ordinary zeta and logarithm-weighted series values at fixed
`sigma>3` and rational height. Define fixed computed caps

```
U = 4 + complexL1(M(1)),
V = 2 + complexL1(Z_0(1)).
```

They are rational and positive. For independent requests
`0<eM,eO,eL<=1`, the theorem
`lw-complex-dirichlet-series-product` proves

```
disk(M(eM)*Z_0(eO)-Z_log(eL), V*eM+U*eO+eL).
```

Thus the actual native Cauchy names satisfy the product identity.
The caps depend only on the fixed evaluation point, not on these
three requests.

`dirichlet-series-ratio.lisp` uses the ordinary zeta reciprocal cap 4
and the existing ratio evaluator `R(e)`. For `0<eM<=1` and any
`eR>0`, it proves

```
disk(M(eM)-R(eR), 4*V*eM+4*(U+1)*eR).
```

For target `E>0`, the computed common request

```
q = min(1, E/(1+4*V+4*(U+1)))
```

gives `disk(M(q)-R(q),E)`. This identifies the Mangoldt and
zeta-series-ratio Cauchy names.

`mellin-zeta-series.lisp` then normalizes the ratio using the actual
transform factors and Euler lower evaluator. With `s=sigma+i*H`,
it computes `q=dirichletSeriesRatioPrecision(sigma,H,E/2)` and

```
B(E) = R(q)/(s*(s-1)) - 1/(s-1)^2
       + (1+lowerEuler(q))/(s-1).
```

The constructor proves `4*q<=E/2`. The normalized ratio is rational
complex, has Cauchy radius `E1+E2`, and satisfies the actual improper
Mellin comparison

```
disk(I(s,E1)-B(E2), 5*E1+E2).
```

These are arithmetic identities for the computed families. The native
derivative identities are proved below. Analytic interpretation,
continuation of the Mellin model into the zero region, and the general
models required by Landau remain open obligations.

### Euler continuation cells and dyadic blocks

These bounds are proved for the actual native evaluators at rational
`s=sigma+i*H`, with `sigma>0` and common point request `0<q<=1`.
Write `E_n(q)` for the existing computed `n^(-s)` sample and set

```
K = sigma+abs(H),
C = K+2*K^2.
```

`exp-quadratic-decay.lisp` proves
`upperExp(v,q)>=v^2/2` and `lowerExpNeg(v,q)<=2/v^2` for positive
`v`. `complex-damping-cap.lisp` retains that damping factor when
comparing the actual reciprocal-times-phase sample with the complex
exponential. The comparison costs the sum of the three independent
requests. With all three equal to `q`, the cap is `2/v^2+3*q`.

Dyadic logarithm growth gives
`lowerLog(n,q)>=j/4` when `j>=2` and `n>=2^j`.
`dirichlet-dyadic-decay.lisp` therefore proves

```
disk(E_n(q), 32/(sigma^2*j^2)+3*q).
```

The logarithm cell at `r=1+1/n` has computed lower value
`ell=lowerLog(r,q)`. `log-cell-bounds.lisp` proves

```
0 <= ell <= 1/n,
abs(1-(n+1)*ell) <= 1/n+(n+1)*q.
```

For `n>=K`, the native exponential first-order bound applies to
`-s*ell`. The actual factor constructed in `complex-euler-cell.lisp`
satisfies

```
G_n(q) = s+(n+1)*(expSample(-s*ell,q)-1),
disk(G_n(q), C/n+(K+1)*(n+1)*q).
```

`euler-dirichlet-cells.lisp` defines the actual correction

```
F_n(q) = s*E_n(q)+(n+1)*(E_(n+1)(q)-E_n(q)).
```

Let `B_x=lw-dirichlet-product-cap(sigma,H,x)`, and define computed costs

```
P_n = (n+1)*(B_n+B_(1+1/n)+66+6*K),
R_n = 3*C/n+2*(K+1)*(n+1)+P_n.
```

Actual complex-power multiplication proves
`disk(F_n(q)-E_n(q)*G_n(q),P_n*q)`.
Using both the damping bound and the unit cap 2 avoids a
non-decaying first-order remainder. For natural
`n>1`, `n>=K`, `j>=2` and `n>=2^j`, the result is

```
disk(F_n(q), 32*C/(sigma^2*j^2*n)+R_n*q).
```

`euler-dirichlet-prefix.lisp` uses the actual common-precision ordinary
prefix `Z_N(q)`, including its exact term 1, to define

```
H_N(q) = (s-1)*Z_N(q)+(N+1)*E_(N+1)(q).
```

For every positive natural `N`, the exact finite telescope is

```
H_N(q) = H_1(q)+sum_(n=2..N) F_n(q).
```

`euler-dirichlet-blocks.lisp` sums the actual corrections over
`n=2^j,...,2^(j+1)-1`. Their reciprocal cell masses sum to at most
1. For `2^j>=K`, it proves

```
disk(sum_(n=2^j..2^(j+1)-1) F_n(q),
     32*C/(sigma^2*j^2)+q*sum_(n=2^j..2^(j+1)-1) R_n).
```

The rounding sum is a terminating rational constructor. Full finite
tails, precision transport and a computed Cauchy value are constructed
below. Arithmetic overlap agreement is proved below as well; analytic
meaning and derivative interpretation remain required.

### Computed Euler tails and a Cauchy evaluator

Let `Q_j(q)=H_(2^j-1)(q)` and retain `K,C` from the preceding section.
`euler-dirichlet-telescoping.lisp` proves exact segment telescoping and

```
Q_(j+1)(q)-Q_j(q) = sum_(n=2^j..2^(j+1)-1) F_n(q).
```

Write `D=32*C/sigma^2` and let `T(L,J)` be the computed sum of the
block rounding costs for `j=J,...,L-1`.
`euler-dirichlet-tail.lisp` sums the actual blocks exactly. For natural
`2<=J<=L`, `2^J>=K` and `0<q<=1`, it proves

```
disk(Q_L(q)-Q_J(q), D/(J-1)+T(L,J)*q).
```

The sharper intermediate bound retains the finite reciprocal-square
tail. Its telescope supplies the displayed uniform bound.

`euler-dirichlet-tail-budget.lisp` defines terminating rational
constructors, using the existing bounded rational ceiling:

```
c(E) = 2+ceil(K)+ceil(2*D/E),
p(cost,E) = min(1,E/(2+2*cost)).
```

For positive `E`, `c(E)` is natural and at least 2. Any natural
`J>=c(E)` satisfies `2^J>=K` and `D/(J-1)<=E/2`.
For nonnegative rational `cost`, the point request `p(cost,E)`
is positive, at most 1, and obeys `cost*p(cost,E)<=E/2`.
Thus any `0<q<=p(T(L,J),E)` gives

```
disk(Q_L(q)-Q_J(q),E),  L>=J>=c(E).
```

`euler-dirichlet-precision.lisp` proves point-precision transport
throughout `sigma>=0`. Set

```
S = 2*K+32,
W_N = (K+1)*N*S+(N+1)*S,
U_j = W_(2^j-1).
```

The actual ordinary prefix at count `N` has independent-request
error at most `N*S*(q1+q2)`. The Euler prefix, including its explicit
boundary term, satisfies

```
disk(H_N(q1)-H_N(q2),W_N*(q1+q2)),  N>=1.
```

Consequently `Q_j` has the same bound with cost `U_j`, for `j>=2`.
These bounds require positive point requests; they do not require
`sigma>3`.

`euler-continuation.lisp` constructs the candidate pole-removed value
for every rational `sigma>0`, rational height and positive `E`:

```
J(E) = c(E/4),
q(E) = p(U_(J(E)),E/4),
V(E) = Q_(J(E))(q(E)).
```

The constructor proves `U_(J(E))*q(E)<=E/8` and
`D/(J(E)-1)<=E/8`. For any natural `L>=J(E)` and `0<d<=1`,
define the computed comparison cost

```
A(L,E) = U_(J(E))+T(L,J(E)).
```

Precision transport and the actual tail bound prove

```
disk(V(E)-Q_L(d),E/4+A(L,E)*d).
```

For independent positive `E1,E2`, the common comparison is computed:

```
L = max(J(E1),J(E2)),
d = p(A(L,E1)+A(L,E2),(E1+E2)/2).
```

Both comparisons and their rounding budgets then prove the exported
Cauchy theorem

```
disk(V(E1)-V(E2),E1+E2).
```

Every value, cutoff and request is a finite rational computation.
This constructs the Euler Cauchy name on the positive half-plane.
Arithmetic overlap agreement and reciprocal normalization are proved
below, along with arithmetic derivative estimates and native identities.
Analytic meaning and general Landau models remain open. No analytic
continuation or limit axiom is added.

### Native zeta agreement and reciprocal normalization

Let `Z_0(e)` be the existing ordinary native zeta series and define
the actual pole-removed series value

```
Y(e) = (s-1)*Z_0(e),  K=sigma+abs(H),  A=K+1.
```

For `sigma>3`, `euler-zeta-prefix.lisp` proves its rationality and
Cauchy radius `A*(e1+e2)`. Define the computed boundary cost

```
B_n = dirichletCubicNodeCost(sigma,H,n)+6*expLipschitzCap(n).
```

For `N>=dirichletSeriesCount(eZ)`, positive `delta` and
`0<q<=min(1,nativeRefinement(N,delta))`, the actual prefix satisfies

```
disk(H_N(q)-Y(eZ),
     A*(3*eZ/8+delta)+2/(N+1)^2+B_(N+1)*q).
```

This uses the already proved cubic point bound with weight `N+1`.
The explicit boundary is not dropped by an assumed limit identity.

`euler-zeta-budget.lisp` computes one common dyadic block count and
request for the Euler value `V(eV)` and native series:

```
L = max(2,J(eV),dirichletSeriesCount(eZ),ceil(2/delta)),
n = 2^L,  N=n-1,
C = eulerComparisonCost(L,eV)+B_n,
q = min(nativeRefinement(N,delta),p(C,2*delta)).
```

The constructors prove `N>=dirichletSeriesCount(eZ)`,
`2/n^2<=delta`, `0<q<=1` and `C*q<=delta`.
Combining the two actual prefix comparisons gives

```
disk(V(eV)-Y(eZ),
     eV/4+3*A*eZ/8+(K+3)*delta).
```

`euler-zeta-agreement.lisp` removes `delta` using the existing
computed rational disk-gap refinement. Thus, for independent positive
requests, the exported overlap identity is

```
disk(V(eV)-Y(eZ),eV/4+3*A*eZ/8).
```

For any positive target `E`, the computed shared request
`q=p(1/4+3*A/8,E)` gives `disk(V(q)-Y(q),E)`.
This identifies the two rational Cauchy names on `sigma>3`.

`zeta-euler-value.lisp` performs exact rational reciprocal
normalization. For rational `sigma>0`, rational height and `s!=1`,
write

```
r = reciprocal(s-1),
R = 1+complexL1(r),
mu(E) = E/R,
Z_E(E) = r*V(mu(E)).
```

The cap `R` is rational and at least 1; `disk(r,R)`.
The point request is positive and obeys `R*mu(E)=E`.
The resulting normalized value is rational complex and has the
certified Cauchy bound

```
disk(Z_E(E1)-Z_E(E2),E1+E2).
```

On `sigma>3`, exact reciprocal cancellation and the pole-removed
overlap identity prove

```
disk(Z_E(eE)-Z_0(eZ),eE/4+3*R*A*eZ/8).
```

The shared request `q=p(1/4+3*R*A/8,E)` gives error at most `E`.
All caps and precisions are computed from the fixed point and target
error. This establishes arithmetic agreement with the native zeta
series. Arithmetic derivative estimates and native identities are proved
below; analytic meaning and uniform models for the full Landau reduction
are still required.

### Uniform Euler polynomial approximants

The six books from `euler-fixed-truncation.lisp` through
`euler-uniform-polynomial.lisp` construct finite rational polynomials
approximating the actual pole-removed Euler Cauchy name `V(s,e)`.
This is a uniform arithmetic approximation theorem. Its derivative
connections are proved below; analytic interpretation remains open.

First, fixed truncation removes the dependence of the prefix cutoff on
the evaluator's requested accuracy. For any `e>0`, `q>0`, integer
`L>=2` and `2^L>=sigma+abs(H)`, it proves

```
disk(V(s,e)-Q_L(s,q), e/4+D(s)/(L-1)+U_L(s)*q).
```

Here `Q_L`, `D` and `U_L` are the actual dyadic prefix, tail cap
and transport cost defined above. The proof compares both values at a
computed later cutoff, then removes the auxiliary point precision by
rational disk-gap refinement. The prefix may be fixed before choosing
`e`.

Fix rational center `s0=sigma0+i*H0` and radius
`0<=r<sigma0`. For every rational offset `z` in that disk, use

```
a = sigma0-r,
h = abs(H0)+3*r,
B = sigma0+abs(H0)+2*r,
A = B+1.
```

The synthetic point `(a,h)` uniformly dominates the tail and
transport costs at `s0+z`. It supplies one block cutoff
`L=diskCutoff(s0,r,targetE)` and point precision
`q<=p(U_L(a,h),targetE)` for the entire disk, giving

```
disk(V(s0+z,e)-Q_L(s0+z,q), e/4+targetE).
```

The same `B` bounds the affine exponential argument
`-(s0+z)`; `A` bounds `s0+z-1`.

To construct the polynomial rather than assume its existence, freeze
the actual logarithm samples at request `q`. The ordinary prefix
has nodes `(lowerLog(n,q),1)` for `n=N,...,2`, with the exact
constant 1 retained separately. The boundary has the single node
`(lowerLog(N+1,q),N+1)`. Their common-precision exponential mixtures
satisfy exactly

```
H_N(s,q) = (s-1)*(1+ordinaryMixture(-s,q))+boundaryMixture(-s,q).
```

For an arbitrary existing exponential mixture of mass `M`, its
computed affine polynomial differs from its common-precision value
by at most `3*epsilon/2+M*q`. The proof accounts for the original
per-node precisions and both polynomial truncation and rounding errors.
The actual ordinary and boundary masses are `N-1` and `N+1`.

Polynomial addition, affine composition and multiplication by the
linear factor `s0+z-1` then construct the finite Euler polynomial.
For ordinary and boundary polynomial budgets `eO,eB`, its error
against the actual `H_N(s0+z,q)` is at most

```
A*(3*eO/2+(N-1)*q)+3*eB/2+(N+1)*q.
```

For a requested finite-prefix error `F>0`, set
`eO=F/(4*A)`, `eB=F/4` and
`C=A*(N-1)+(N+1)`. Any positive
`q<=p(C,F/2)` makes that error at most `F`.

Finally, for total target `E>0`, choose

```
L = diskCutoff(s0,r,E/2),
N = 2^L-1,
q = min(p(U_L(a,h),E/2),p(C,E/4)).
```

Use the finite-prefix polynomial with error `F=E/2`.
The constructor `lw-euler-uniform-polynomial` returns its rational
coefficient list, with a caller-specified natural minimum degree.
Its coefficients, cutoff, logarithm samples and point request depend
only on the center, disk, target degree and `E`. They are independent
of the offset and the Euler evaluator's accuracy. The theorem
`lw-complex-euler-uniform-polynomial-comparison` proves

```
disk(P_E(z)-V(s0+z,e), E+e/4)
```

for every rational `z` in the disk and every independent `e>0`.
Comparing two polynomials through the same Euler value and removing
its auxiliary accuracy by a computed rational disk gap proves

```
disk(P_E1(z)-P_E2(z), E1+E2).
```

Their minimum-degree requests may differ. These bounds supply uniform
polynomial data for finite Cauchy coefficient extraction. The coefficient
names, fixed caps, derivative estimates and local-series reconstruction
are constructed below. Native derivative identities are also proved
below; actual zeta factor models remain required.

### Euler coefficient Cauchy names and fixed disk caps

`polynomial-coefficient-maps.lisp` supplies exact arithmetic maps
for rescaling and zero padding. With `P(z)` given by a finite
coefficient list, the rescaled list evaluates to `P(r*w)` and its
coefficient `k` is exactly `r^k` times the original coefficient.
Padding to any longer list preserves every coefficient and evaluation;
out-of-range coefficients are explicitly zero.

Fix a rational disk `0<r<sigma0`. Write
`P_(t,E)` for the uniform polynomial above with minimum-degree
request `t` and error `E`, and set

```
Q_(t,E)(w) = P_(t,E)(r*w),
b_(t,k)(E) = coefficient k of Q_(t,E),
b_k(E) = b_(k,k)(E).
```

These are finite rational constructors. To compare independent
`t1,t2,E1,E2`, pad both rescaled polynomials to

```
m = 1+max(k,len(P_(t1,E1)),len(P_(t2,E2))).
```

Their exact difference polynomial `D` has length `m`, and
the already proved uniform approximation gives boundary cap
`E1+E2` at every rational unit-disk point. Induction constructs
the entire finite `lw-cauchy-boundary-check` for every requested
sample count. In particular it supplies the computed sample count
used by the finite coefficient theorem, with degree `m` and any
auxiliary error `delta>0`.

That theorem bounds the actual difference of coefficient `k`
by `E1+E2+delta`. Rational disk-gap refinement removes
`delta`, yielding

```
disk(b_(t1,k)(E1)-b_(t2,k)(E2), E1+E2).
```

The minimum degrees and precisions may differ; no agreement of
list lengths or lower bound on the degree relative to `k` is
assumed. The canonical `b_k(E)` therefore has Cauchy radius
`E1+E2`.

`euler-coefficient-bounds.lisp` computes one fixed cap from
a coarse polynomial:

```
M = coefficientMass(Q_(0,1)),
C = 2+M.
```

For every `t,E>0` and unit-disk point `w`, comparison with
`Q_(0,1)` proves

```
disk(Q_(t,E)(w), C-1+E).
```

Finite Cauchy extraction and removal of its auxiliary error transfer
this same bound to every `b_(t,k)(E)`. In particular,

```
disk(b_k(E),C)   when 0<E<=1.
```

The cap `C` depends only on the center and disk radius. It is
independent of `k`, degree request and precision. It comes from
one computed finite coefficient mass, not an assumed analytic bound.

Finally, `euler-local-coefficients.lisp` converts to the original
complex coordinate. For coefficient `k`, define

```
R = r^k > 0,
q_k(e) = min(1,e*R),
a_k(e) = b_k(q_k(e))/R.
```

The request is positive and rational, is at most 1, and satisfies
`q_k(e)/R<=e`. Exact scaling identifies `a_k(e)` with
coefficient `k` of the actual polynomial `P_(k,q_k(e))`.
The exported theorems prove

```
disk(a_k(e1)-a_k(e2),e1+e2),
disk(a_k(e),C/r^k).
```

These bounds hold for every positive `e,e1,e2`. The resulting
coefficient names and geometric cap support the local series reconstruction
proved below, along with native zeta derivative identities. Analytic
interpretation and general-zero model applicability remain required.
Explicit Euler derivative estimates follow first.

### Euler quadratic increments and a computed derivative modulus

The four books from `polynomial-quadratic-bounds.lisp` through
`euler-difference-quotient.lisp` prove a local derivative estimate
for the actual Euler evaluator, using the coefficient cap above.

The finite predicate `lw-polynomial-coefficient-caps` checks
every coefficient against a common disk. Its computed first failed
index witnesses a rejected check. The proved coefficient bound for
the actual Euler polynomial therefore discharges this whole check;
it is not an added analytic hypothesis.

For a finite polynomial whose coefficients have cap `M`, every
tail beginning at degree `k` has radius `2*M*h^k` when
`disk(w,h)` and `0<=h<=1/2`. Exact finite algebra gives

```
P(w)-P(0)-coefficient(P,1)*w = polynomial(cddr(coefficients(P)),w,2).
```

Consequently its quadratic remainder has radius `2*M*h^2`,
including empty and constant polynomials.

Fix the disk `0<r<sigma0` and its cap `C` from the preceding
section. Write `V` for the actual pole-removed Euler value,
`b_1` for its normalized first coefficient name and `a_1`
for the physical coefficient name. For `disk(w,h)`,
`h<=1/2` and independent positive errors `eS,e0,eB`, the
arithmetic theorem proves

```
disk(V(s0+r*w,eS)-V(s0,e0)-b_1(eB)*w,
     2*(C-1)*h^2+eS/4+e0/4+eB*h).
```

The proof first uses one uniform polynomial at auxiliary precision
`E`. Its total extra radius is
`(2+h+2*h^2)*E`. A computed rational disk gap removes `E`.
No differentiability assumption enters this argument.

Conversion to physical coordinates defines the computed curvature

```
K = 2*(C-1)/r^2 > 0.
```

For `disk(z,delta)`, `delta<=r/2`, and independent positive
`eS,e0,eD`, `lw-complex-euler-quadratic-increment` proves

```
disk(V(s0+z,eS)-V(s0,e0)-a_1(eD)*z,
     K*delta^2+eS/4+e0/4+eD*delta).
```

The radius adjustment uses the already computed request
`q_1(eD)<=eD*r`, so the physical slope is exactly the constructed
first coefficient rather than additional derivative data.

For target `E>0`, the step constructor is

```
eta(E) = min(r/2,p(K,E/2)).
```

It is positive and rational, is at most `r/2`, and satisfies
`K*eta(E)<=E/4`. For `0<delta<=eta(E)`, value errors
`eS,e0<=E*delta` and slope error `eD<=E/4` make the
increment radius at most `E*delta`. The computed theorem uses
`eS=e0=E*delta` and `eD=E/4`; the refined theorem accepts
independently finer positive requests.

Finally, a nonzero rational complex step has a computed size

```
lambda = abs(Re(z))+abs(Im(z)) > 0.
```

Finite coordinate inequalities prove `disk(z,lambda)` and
`(lambda/2)^2<=normSquare(z)`, hence its reciprocal has cap
`2/lambda`. For `lambda<=eta(E/2)`, choose point precision
`q=E*lambda/2`. Exact division of the linear remainder gives

```
disk((V(s0+z,q)-V(s0,q))/z-a_1(E/8), E).
```

This is `lw-complex-euler-computed-difference-quotient`. It
proves the first physical coefficient's derivative approximation
property for every sufficiently small nonzero rational complex step,
with all thresholds and requests computed from the disk and error.
The coefficient name itself already has Cauchy radius `e1+e2`.

Local power-series reconstruction and native derivative identities are
proved below. Analytic interpretation and the general factor/zero models
needed by Landau remain open.

### Local power-series reconstruction of the Euler value

`polynomial-prefix-bounds.lisp`, `euler-series-coefficients.lisp`
and `euler-local-series.lisp` recover the actual Euler evaluator
from the canonical coefficient names.

For a finite coefficient list, zero padding acts as truncation when
the requested count is shorter than the list. The generic prefix
identity is exact:

```
P(coefficients,w,offset)-P(pad(coefficients,N),w,offset)
 = P(drop(coefficients,N),w,offset+N).
```

Every prefix coefficient at index `k<N` is exactly the original
coefficient, with zero used outside the original list. Dropping a
prefix preserves the common coefficient cap. The existing finite
tail theorem therefore bounds the remainder by `2*M*h^N`
when the list has cap `M` and `disk(w,h)`, `h<=1/2`.

Fix the disk `0<r<sigma0` and cap `C` above. Using the
canonical normalized coefficient names `b_k(q)`, define the
finite sum

```
B_N(w,q) = sum_(k<N) b_k(q)*w^k.
```

The coefficient list, its length and each indexed entry are
constructed explicitly. Its comparison with the padded prefix of
an independently requested `Q_(t,E)` has coefficient cap `q+E`.
A computed first failed coefficient reduces the entire finite cap
check to the already proved independent-degree coefficient estimate.

On `disk(w,1/2)`, the prefix difference has radius `2*(q+E)`.
The rest of `Q_(t,E)` has radius `2*(C-1+E)*2^(-N)`.
Composition with the Euler value comparison gives

```
disk(B_N(w,q)-V(s0+r*w,eV),
     2*q+2*(C-1)*2^(-N)+eV/4+(3+2*2^(-N))*E).
```

Rational disk-gap refinement removes the auxiliary polynomial
request `E`. Thus for every natural `N` and independent
positive `q,eV`,

```
disk(B_N(w,q)-V(s0+r*w,eV),
     2*q+2*(C-1)*2^(-N)+eV/4).
```

The computed local series constructor chooses

```
q(E) = min(1,E/8),
N(E) = resolventTruncationCount(1/2,E/(8*(C-1))),
S(w,E) = B_(N(E))(w,q(E)).
```

The count is a positive natural and the coefficient request is
positive, rational and at most 1. The certified budgets are

```
2*q(E) <= E/4,
2*(C-1)*2^(-N(E)) <= E/4.
```

Consequently `lw-complex-euler-local-series-value-agreement`
proves

```
disk(S(w,E)-V(s0+r*w,eV), E/2+eV/4).
```

Both the cutoff and coefficient request depend on the fixed disk
and target `E`, independently of `w` and `eV`. The same
finite coefficient list works everywhere in the half disk.

Comparing two series requests through the same Euler value and
removing its auxiliary accuracy gives the stronger Cauchy bound

```
disk(S(w,E1)-S(w,E2), (E1+E2)/2).
```

This constructs a local power-series representation of the actual
Euler Cauchy name. Native derivative identities are proved below;
analytic interpretation, actual factor models and complete zero covers
remain required for Landau.

### Arbitrary inner disks and fixed series caps

The half-disk interface above remains available.
`polynomial-geometric-bounds.lisp` and `euler-inner-series.lisp`
extend the construction to every rational `0<=h<1`, with
`disk(w,h)`. Define the computed geometric gain

```
g(h) = 1/(1-h).
```

For any finite polynomial with coefficient cap `M`, its tail from
degree `N` has radius `M*g(h)*h^N`. The exact prefix/drop
identity transfers this estimate to its padded truncation.

For the canonical Euler prefix `B_N(w,q)`, an independently
requested polynomial `Q_(t,E)` gives comparison radius

```
(q+E)*g(h)+(C-1+E)*g(h)*h^N.
```

Composition with the actual Euler value and rational disk-gap
refinement remove the auxiliary polynomial error. The result is

```
disk(B_N(w,q)-V(s0+r*w,eV),
     q*g(h)+(C-1)*g(h)*h^N+eV/4).
```

The removed error has the explicit gain
`1+g(h)+g(h)*h^N`, fixed before the auxiliary request is chosen.

For target `E>0`, the constructors choose

```
q_h(E) = min(1,E*(1-h)/4),
N_h(E) = resolventTruncationCount(h,E/(4*(C-1))),
S_h(w,E) = B_(N_h(E))(w,q_h(E)).
```

Their proved budgets are

```
q_h(E)*g(h) <= E/4,
(C-1)*g(h)*h^(N_h(E)) <= E/4.
```

Thus `lw-complex-euler-inner-series-value-agreement` and the
Cauchy theorem give

```
disk(S_h(w,E)-V(s0+r*w,eV), E/2+eV/4),
disk(S_h(w,E1)-S_h(w,E2), (E1+E2)/2).
```

All requests and counts depend on the fixed center, outer radius
`r`, inner parameter `h` and target error. The entire computed
coefficient list works uniformly throughout the chosen inner disk.

The canonical coefficients at requests at most 1 have cap `C`.
The general geometric bound therefore also proves

```
disk(S_h(w,E), C/(1-h)).
```

This cap is independent of requested precision and truncation degree.
The physical evaluation disk has radius `r*h`, which may approach
any outer radius `r<sigma0`. These bounds support contour models
without a half-disk restriction; actual zeta factor and zero-cover
model construction remains required.

### Finite polynomial derivative coefficients

`polynomial-derivatives.lisp` constructs the formal finite
derivative by the Horner recursion

```
D([],z) = 0,
D([a0]+tail,z) = P(tail,z)+z*D(tail,z).
```

It returns a rational complex value for every valid coefficient list
and rational complex point. The exact affine coefficient identities are

```
coefficient(P(center+slope*w),0) = P(center),
coefficient(P(center+slope*w),1) = slope*D(P,center).
```

Adding a constant preserves coefficient 1. Multiplication by a linear
factor satisfies the exact finite product rule

```
coefficient((constant+slope*w)*P(w),1)
 = constant*coefficient(P,1)+slope*coefficient(P,0).
```

The statements include empty and constant polynomials.
`polynomial-sum-coefficients.lisp` also proves coefficient extraction
commutes with polynomial addition, including zero padding, and the
constant-coefficient rule for adding a constant.

### Weighted exponential derivatives and native Euler sums

`exp-mixture-derivatives.lisp` constructs the derivative nodes of a
finite exponential mixture. A node `(lambda,base)` becomes
`(lambda,lambda*base)`; rates remain nonnegative rationals and the node
count is unchanged. Write `W(nodes)` for this constructor. For the
existing coefficient constructor `c_k(nodes)`, the exact recurrence is

```
(k+1)*c_(k+1)(nodes) = c_k(W(nodes)).
```

The formal derivative of the degree-`d` mixture polynomial is therefore
exactly the degree-`d-1` polynomial of `W(nodes)`. The book also proves
the offset version and the corresponding first coefficient after affine
substitution.

`exp-mixture-derivative-bounds.lisp` chooses

```
derivativeDegree(nodes,R,e)
 = 1+rawDegree(W(nodes),R,mixtureBudget(W(nodes),e)).
```

For any degree `d` at least this positive computed integer, the actual
degree-`d` polynomial `P_d` and common-precision mixture value `M_q`
satisfy, throughout `disk(z,R)`,

```
disk(D(P_d,z)-M_q(W(nodes),z), 3*e/2+mass(W(nodes))*q).
```

The affine first coefficient has the same bound multiplied by a disk
cap for the slope. The ordinary polynomial request may be independent
of this derivative request; the caller may select the target degree
after fixing the nodes and their common precision.

`euler-weighted-mixtures.lisp` identifies the weighted ordinary Euler
nodes exactly with the existing common-precision log-weighted prefix.
For `N>=1`, `q>0`, and `lambda_n=lowerLog(n,q)`,

```
M_q(W(ordinaryNodes(N,q)),-s) = commonLogPrefix(s,N,q),
mass(W(ordinaryNodes(N,q))) <= N^2,
M_q(W(boundaryNodes(n,q)),-s) = n*lambda_n*E_n(s,q),
mass(W(boundaryNodes(n,q))) = n*lambda_n <= n^2.
```

Here `E_n` is the actual frozen-logarithm exponential sample. The mass
bounds are independent of `q`.

`euler-prefix-derivatives.lisp` computes one target degree covering
both weighted node families. For the existing centered Euler prefix
polynomial `P_N(w)`, it compares `coefficient(P_N,1)` with the actual
finite derivative expression

```
J_N(s,q) = commonOrdinaryPrefix(s,N,q)
           -(s-1)*commonLogPrefix(s,N,q)
           -(N+1)*lambda_(N+1)*E_(N+1)(s,q).
```

Let `K=sigma+abs(height)+1`, let `o>0` be the ordinary polynomial
request, and let `d>0` be the derivative request. The explicit radius is

```
R_P = K*(3*d/2+N^2*q)
      +3*o/2+(N-1)*q+3*d/2+(N+1)^2*q.
```

The argument cap must contain the rational center `-s`, and the
target must be at least the computed common derivative degree.
The boundary polynomial's value request remains an independent
positive parameter.

`euler-derivative-series.lisp` controls the upper derivative boundary
for `sigma>3` and `0<q<=1`. For rational `n>1`, set

```
B(s,n) = n^2*(cubicNodeCost(s,n)+6*expLipschitzCap(n)).
```

This cost is positive and rational, and

```
disk(n*lambda_n*E_n(s,q), 2/n+B(s,n)*q).
```

Thus the extra logarithm in the derivative boundary still permits
decay. Define the native candidate from the actual two series values:

```
D_native(s,e) = Z0(s,e)-(s-1)*Z1(s,e).
```

It is a rational Cauchy name, with independent-request bound

```
disk(D_native(s,e1)-D_native(s,e2), (K+1)*(e1+e2)).
```

For `N>=seriesCount(e)`, `t>0`, and
`0<q<=min(1,nativeRefinement(s,N,t))`, the finite derivative satisfies

```
disk(J_N(s,q)-D_native(s,e), R_N),
R_N = (K+1)*(3*e/8+t)+2/(N+1)+B(s,N+1)*q.
```

The theorem `lw-euler-prefix-polynomial-native-derivative-comparison`
composes both comparisons, giving radius `R_P+R_N` for the first
coefficient of the actual finite Euler polynomial against this native
candidate.

The canonical local Euler slope is identified with this native
candidate by the constructions below.

### Refinable Euler polynomials and coefficient extraction

`euler-refined-polynomial.lisp` keeps the dyadic block `J`, common
point request `q` and target degree `T` independently selectable.
For `N=2^J-1`, it constructs the same finite Euler prefix polynomial
using argument cap `sigma+abs(height)+2*r`, ordinary request
`ordinaryError(s,r,E/2)` and boundary request `E/8`.

For `0<r<sigma`, `E>0`, `J>=diskBlockCutoff(s,r,E/2)`, and
`J>=2`, define

```
refinedRequest(s,r,J,E)
 = min(roundingPrecision(diskTransportCost(s,r,J),E/2),
       polynomialPrecision(s,r,2^J-1,E/2)).
```

This request is positive. Every finer positive `q` gives, throughout
the physical disk `disk(w,r)`,

```
disk(P_refined(w)-V(s+w,eV), E+eV/4).
```

Comparison with any independently requested canonical uniform
polynomial has radius `E+E_canonical`; the auxiliary value error
has been removed by rational disk-gap refinement.

`euler-refined-coefficients.lisp` rescales and pads the difference
polynomial, constructs each finite Cauchy boundary check and extracts
any selected normalized coefficient. Removing the extraction margin
preserves radius `E+E_canonical`. For the first physical coefficient,
the canonical coefficient request and reciprocal-radius scaling give

```
disk(coefficient(P_refined,1)-a1(s,r,eD), E/r+eD).
```

Here `a1` is the existing `lw-complex-euler-local-coefficient-value`
at index 1. Its quadratic increment and difference-quotient estimates
were already proved. Boundary-check acceptance is constructed for the
actual polynomial difference.

### Native Euler derivative agreement

`euler-derivative-alignment.lisp` chooses all auxiliary data from
`s`, physical radius `0<r<sigma`, native request `eN>0` and a
temporary margin `m>0`. This comparison requires only `sigma>3`
at the center; the surrounding disk may approach the imaginary axis.

Write `K=sigma+abs(height)+1`, `A=K+1`, and use the existing
rounding constructor, which guarantees `cost*request<=error/2`:

```
E = roundingPrecision(1+1/r,m/4),
d = roundingPrecision(3*A/2,m/4),
t = roundingPrecision(A,m/4).
```

All are positive rationals, and

```
E+E/r <= m/8,   3*A*d/2 <= m/8,   A*t <= m/8.
```

Choose

```
J = max(diskBlockCutoff(s,r,E/2),
        eulerZetaComparisonCutoff(s,eN,eN,m/8)),
N = 2^J-1.
```

The computed block guarantees `N>=seriesCount(eN)` and
`2/(N+1)<=m/8`. Define the total point cost

```
M = K*N^2+(N-1)+(N+1)^2+B(s,N+1).
```

It is positive and independent of the point request. Set

```
q = min(refinedRequest(s,r,J,E),
        nativeRefinement(s,N,t),
        roundingPrecision(M,m/4)).
```

This positive request satisfies all uniform-polynomial and native-series
comparison bounds, as well as `M*q<=m/8`. Only then choose
`T=eulerDerivativeTarget(N,q,argumentCap,d)`. The first-coefficient
comparison and native derivative comparison now use the same polynomial.
The book proves their full auxiliary radius, including `E/r`, is at
most `m`.

`euler-native-derivative.lisp` composes those bounds and removes
`m` by rational disk-gap refinement. For independent positive
`eD,eN`, rational `sigma>3`, rational height, and `0<r<sigma`,

```
disk(a1(s,r,eD)-D_native(s,eN), eD+3*A*eN/8).
```

This is the theorem `lw-complex-euler-native-derivative-agreement`.
It identifies the canonical local Euler slope with
`Z0-(s-1)*Z1` as Cauchy names. For every target `e>0`, the computed
common request

```
q = min(e/2,roundingPrecision(A,e))
```

also proves `disk(a1(s,r,q)-D_native(s,q),e)`.

### Derivative of the normalized zeta evaluator

`complex-quotient-increments.lisp` proves a rational reverse triangle
bound for the complex `L1` size. If `c!=0` and
`L1(h)<=L1(c)/2`, then `c+h!=0`, its squared norm is at least
`L1(c)^2/16`, and its reciprocal has cap `1/(L1(c)/4)`.

Under that clearance, for `h!=0` and finite rational complex values
`v_h,v_0`, it proves the exact identity

```
((v_h/(c+h)-v_0/c)/h) = (((v_h-v_0)/h)-v_0/c)/(c+h).
```

Thus the existing quotient-error estimate transfers an Euler difference
quotient to the reciprocal-normalized evaluator with explicit denominator
clearances.

`zeta-euler-derivative.lisp` constructs a derivative Cauchy name.
For `s!=1`, write `c=s-1`, `lambda=L1(c)>0`, and let
`C=lw-zeta-euler-inverse-cap(s)>=1`. Define

```
L = 1/(lambda/4),   R = 1/(lambda/2),
M = 2*C+L*(9+4*C),
p(e) = roundingPrecision(M,e/2).
```

The computed request is positive, at most 1, and satisfies

```
2*C*p(e) <= e/4,
L*(9+4*C)*p(e) <= e/4.
```

For `0<r<sigma`, the normalized derivative name is

```
T(s,r,e) = (a1(s,r,p(e))-Z_E(s,p(e)))/(s-1).
```

It is rational and has Cauchy radius `e1+e2` throughout `sigma>0`
away from `s=1`. For requests at most 1, the zeta value has the fixed
cap `C_Z=2+L1(Z_E(s,1))`. The derivative numerator therefore has
precision-independent cap

```
N = C_coefficient(s,r)/r+C_Z.
```

### Computed zeta difference quotients

`zeta-difference-quotient.lisp` sets

```
D = N*L*R,
delta(s,r,e)
 = min(1,lambda/2,eulerDerivativeModulus(s,r,4*p(e)),
       roundingPrecision(D,e)).
```

This modulus is positive, at most `r/2`, and satisfies
`D*delta<=e/2`. For every nonzero rational complex step `h` with
`L1(h)<=delta`, use the shared Euler value request

```
q_V = 4*p(e)*L1(h),
e_0 = C(s)*q_V,
e_h = C(s+h)*q_V.
```

Both endpoint requests are positive rationals. Exact reparameterization
of the existing zeta constructor identifies `Z_E(s,C(s)*q_V)` with
`V(s,q_V)/(s-1)`. Applying the Euler difference-quotient theorem at
error `8*p(e)` gives its existing slope `a1(s,r,p(e))` exactly.
The quotient estimate and computed budgets then prove

```
disk((Z_E(s+h,e_h)-Z_E(s,e_0))/h-T(s,r,e), e).
```

This is `lw-complex-zeta-euler-computed-difference-quotient`. Its
endpoints are actual evaluator calls; no analytic derivative hypothesis
is supplied.

### Native normalized derivative identity

`zeta-native-derivative.lisp` uses the already-identified Euler slope
and the native zeta value comparison. For `sigma>3`, set

```
K = sigma+abs(height)+1,   A = K+1,
G = C*(A+C*K).
```

For independent positive requests `eD,eN`, it proves

```
disk(T(s,r,eD)-(-Z1(s,eN)), eD+3*G*eN/8).
```

The actual normalized derivative name is therefore the negative
log-weighted native series as a Cauchy name. For any target `e>0`,
the positive computed request

```
q = min(e/2,roundingPrecision(G,e))
```

also gives `disk(T(s,r,q)-(-Z1(s,q)),e)`.

The arithmetic derivative bridge is now proved. Its logarithmic
derivative and Mellin compositions follow.

### Evaluated zeta clearance and logarithmic derivative

`zeta-euler-clearance.lisp` transfers the native ordinary-series cap
to the actual normalized evaluator. For rational `sigma>3` and
every positive request `e`,

```
disk(Z_E(s,e)-1,1/2+e/4).
```

The native auxiliary request is removed by rational disk-gap refinement.
For `0<e<=1`, this gives squared norm at least `1/16`, a nonzero
denominator and reciprocal cap 4.

`zeta-euler-log-derivative.lisp` uses the fixed derivative numerator
cap `N` above and the inverse cap `C`. The evaluated normalized
derivative `T(s,r,e)` has cap

```
M = C*N >= 2
```

for every positive request. Set

```
H = 4+16*M >= 36,
q_L(e) = roundingPrecision(H,2*e).
```

Then `q_L` is positive, at most 1, and satisfies
`H*q_L<=e` and `16*q_L<=e`. The actual negative logarithmic
derivative name is

```
L(s,r,e) = -T(s,r,q_L(e))/Z_E(s,q_L(e)).
```

Its denominator clearance is proved for the actual evaluator. Quotient
transport gives the Cauchy radius `e1+e2`.

### Agreement with the native logarithmic-derivative ratio

`zeta-native-log-derivative.lisp` compares this value with the existing
native ratio `Q(s,eR)`. Write `K=sigma+abs(height)+1` and use the
native derivative gain `G` from the preceding section. The direct
finite comparison has radius

```
16*q_L(eL)+J*p_N(eR),
J = 3*G/2+18*C*K,
p_N(eR) = min(1/4,eR/104).
```

A separate native-ratio refinement and its Cauchy bound remove the
auxiliary error. For independent positive `eL,eR`,

```
disk(L(s,r,eL)-Q(s,eR),eL+eR).
```

In particular, using `e/2` for both arguments gives radius `e`.
These statements require rational `sigma>3`, rational height and
`0<r<sigma`.

### Actual Mellin and logarithmic-derivative identity

`mellin-zeta-derivative.lisp` uses the same rational transform as the
native Mellin construction, now with the evaluated logarithmic derivative:

```
F_r(s,e) = L(s,r,e/4)/(s*(s-1))
           -1/(s-1)^2+(1+gammaLower(e/4))/(s-1).
```

Its exact constructor is `lw-mellin-zeta-derivative-value`. It is
rational and satisfies

```
disk(F_r(s,e1)-F_r(s,e2),(e1+e2)/2),
disk(F_r(s,eF)-B(s,eB),eF/2+eB/4),
```

where `B` is the existing normalized native ratio value. Composing
with the actual improper Mellin comparison and removing the last native
auxiliary request proves

```
disk(I(s,eI)-F_r(s,eF),5*eI+eF/2).
```

The computed arguments `eI=e/10`, `eF=e` meet any requested
radius `e>0`.

This identity is proved for `sigma>3`. The actual anchor identities
needed for normalization at one are proved below. Analytic interpretation,
model comparisons in the zero region, general factors and complete zero
covers remain required for the full Landau reduction.

### Euler anchor identities at one

The five `euler-anchor-*.lisp` books identify the computed pole-removed
value and its first physical coefficient at `s=1`. These are equalities
of rational Cauchy names, expressed by explicit error bounds:

```
disk(V(1,eV)-1,eV/4),
disk(a1(1,0,r,eD)-(gammaLower(eG),0),eD+eG),  0<r<1.
```

The exported theorems are `lw-complex-euler-anchor-value` and
`lw-complex-euler-anchor-derivative`. In the derivative theorem,
using `eD=eG=e/2` gives radius `e`; this computed refinement is
also proved. The preexisting local difference-quotient theorem
identifies `a1` as the slope of the actual Euler evaluator.

The proof extends the exponential normalization to `rate>=1`.
For integer `n>1`, let `E_n(q)` be the computed rate-one node and set

```
A(n) = logRampCap(1,0,n)+4+2*expLipschitzCap(n),
S(N) = sum_{n=2..N} A(n),
D(N) = S(N)+(N+1)*A(N+1).
```

For `0<q<=1`, the proved endpoint bound is
`disk(n*E_n(q)-1,A(n)*q)`. Scaling and finite induction compare
the ordinary prefix with `H_N` and its derivative `J_N(q)` with
`H_N-logLower(N+1,q)`. Arbitrary harmonic/log enclosures overlap
the existing Euler enclosure, which gives

```
disk(J_N(q)-(gammaLower(eG),0),
     (1+D(N))*q+1/(N+1)+eG).
```

For the value anchor, a computed shared precision aligns this endpoint
with the fixed Euler truncation. For the derivative, the block is
chosen above both the disk cutoff and `2+ceil(8/margin)`.
The common precision is chosen next, followed by the derivative degree.
The cost `2*N^2+(N-1)+(N+1)^2+1+D(N)` controls all finite-node losses.
The coefficient, slope, roundoff and reciprocal-tail budgets have total
at most `margin`. Rational disk-gap refinement removes that margin.

These results discharge the two actual anchor identities required by
the existing normalized factor-model construction. They do not yet
construct general factors or prove their uniform comparisons.

### Checked Euler logarithmic derivative

`euler-value-clearance.lisp` checks one actual coarse Euler value.
For rational `sigma>0`, height and `eta>0`, set

```
lambda = L1(V(s,eta)),  d=lambda/4.
```

The finite predicate `lw-euler-value-clearance-check` requires
`lambda>0` and `eta<=lambda/16`. If it passes, every
`0<q<=d/4` satisfies

```
normSquare(V(s,q)) >= d^2,
V(s,q) != 0,
disk(1/V(s,q),1/d).
```

These follow from the actual Euler Cauchy estimate and the proved
small-shift clearance bound. No separate nonvanishing hypothesis is
supplied for the finer values.

For fixed `0<r<sigma`, `euler-log-derivative.lisp` constructs

```
M = uniformCoefficientCap(s,r)/r,
H = 1/d + M/d^2,
p(E) = min(d/4,roundPrecision(H,2*E)),
W(s,r,eta,E) = a1(s,r,p(E))/V(s,p(E)).
```

The request is positive, at most one, and satisfies `H*p(E)<=E`.
The actual numerator has cap `M` at every positive request. The
constructed quotient is rational and obeys

```
disk(W(s,r,eta,E),M/d),
disk(W(s,r,eta,E1)-W(s,r,eta,E2),E1+E2).
```

For any two accepted coarse requests `eta1,eta2`, the stronger
certificate-independence theorem proves

```
disk(W(s,r,eta1,E1)-W(s,r,eta2,E2),E1+E2).
```

It constructs a common request below both clearance thresholds, with
`(H1+H2)*q<=margin`, then removes the margin by rational disk-gap
refinement. The cap above is fixed for each clearance certificate;
agreement of the values does not assert a cap uniform over contours.

`euler-log-derivative-anchor.lisp` supplies an actual accepted check.
For every `0<eta<=1/64`, the anchor identity proves the check at
`s=1` and gives `255/1024<=d<=1/2`. The quotient then satisfies

```
disk(W(1,r,eta,E)-(gammaLower(eG),0),E+eG),  0<r<1.
```

Taking the fixed coarse request `eta=1/64` and both remaining
requests equal to `e/2` meets radius `e`. This calibration uses the
proved value and derivative anchors. The normalized quotient and its
right-plane Mellin comparison are proved below. The normalized extension
at one is constructed later in this contract; uniform contour models and
analytic interpretation remain open.

### Euler quotient normalization and Mellin agreement

`euler-zeta-clearance.lisp` generates the coarse check throughout
`sigma>3`. With `C=lw-zeta-euler-inverse-cap(s)`, it chooses

```
etaRight(s) = zetaEulerPointError(s,1/64) = 1/(64*C).
```

Writing `lambda=L1(V(s,etaRight))`, the existing zeta clearance
gives `C*lambda>=1/4`. Since `16*C*etaRight=1/4`, this proves
the actual Euler check. No caller-supplied nonvanishing check remains
in the resulting right-plane statements.

`euler-zeta-log-algebra.lisp` proves exact finite identities on
`sigma>0` away from one:

```
(s-1)*ZE(s,e) = V(s,pZ(e)),
(s-1)*T(s,r,e) = a1(s,r,qD(e))-ZE(s,qD(e)).
```

It also computes the nested requests used by the logarithmic derivative.
At its internal request `v`, put `z=ZE(v)`, `zD=ZE(qD(v))`,
`a=a1(qD(v))`, and `N=z+(s-1)*T(v)`. Then

```
N = a+(z-zD),
N/((s-1)*z) = 1/(s-1)-L(s,r,e).
```

Here `L` is the already constructed negative zeta logarithmic
derivative. `euler-zeta-log-derivative.lisp` combines these finite
identities with denominator clearances and Cauchy estimates. For a
fixed accepted Euler check, its comparison cost is

```
K = H+2/d+2*(M+2)/d^2.
```

A computed auxiliary request below both one and `d/4`, followed by
rational disk-gap refinement, proves the independent-request identity

```
disk(W(s,r,eta,eW)-(1/(s-1)-L(s,r,eL)),eW+eL).
```

It holds for `sigma>3`. The generated `etaRight` removes the coarse
check hypothesis, and using both remaining requests `e/2` meets radius
`e`.

`euler-log-transform.lisp` proves the exact normalized formula
`1/s-(w-s*g)/(s*(s-1))` and its rational transport bounds. Let
`C0=C(s+1)` bound `1/s`, let `C1=C(s)` bound `1/(s-1)`,
and define

```
G = C0*C1+C1 >= 2,
q(E) = roundPrecision(G,E),  G*q(E)<=E/2,
F_W(s,r,eta,E) =
  1/s-(W(s,r,eta,q(E))-s*gammaLower(q(E)))/(s*(s-1)).
```

`mellin-euler-log-derivative.lisp` constructs this actual value.
For `sigma>0`, `s!=1`, `0<r<sigma` and accepted coarse checks,
it is rational and satisfies

```
disk(F_W(s,r,eta1,E1)-F_W(s,r,eta2,E2),(E1+E2)/2).
```

Thus its Cauchy name is independent of the accepted check. In the right
half-plane `sigma>3`, the generated check gives

```
disk(I(s,eI)-F_W(s,r,etaRight(s),eF),5*eI+eF/2).
```

The computed requests `eI=e/10`, `eF=e` meet radius `e`.
The normalized extension at one is proved below. Uniform contour and
factor models, complete zero covers and analytic interpretation remain
required.

### Uniform derivative polynomials on inner disks

`polynomial-derivative-coefficients.lisp` constructs the actual weighted
coefficient list of a formal derivative and proves its evaluation identity.
`euler-shifted-polynomial.lisp` shifts one global polynomial
`P=P(s,R,target,E)` to `A_z(u)=P(z+u)`. For
`0<delta<=R<sigma` and `disk(z,R-delta)`, it compares that shift with
every local Euler polynomial on the physical `delta` disk.

`euler-shifted-coefficients.lisp` generates every sample of the finite
boundary check. Cauchy extraction and explicit disk-gap refinement give,
for every natural `k` and positive errors,

```
disk(coefficient(A_z,k)-a_k(s+z,delta,e), E/delta^k+e).
```

Here `a_k` is the actual physical coefficient evaluator, not an input
coefficient list. `euler-coefficient-radii.lisp` compares both extractions
to the same global polynomial and eliminates its auxiliary error:

```
disk(a_k(s,r1,e1)-a_k(s,r2,e2), e1+e2)
    (0<r1,r2<sigma).
```

`euler-uniform-derivative.lisp` uses `0<=r<R<sigma` and defines

```
D(s,R,r,target,epsilon)
  = derivativeCoefficients(P(s,R,target,(R-r)*epsilon/2)).
```

This coefficient list is independent of the evaluation point. For every
`disk(z,r)`, every `0<rho<Re(s+z)` and positive `epsilon,e`,

```
disk(D(z)-a_1(s+z,rho,e), epsilon+e).
```

`euler-uniform-derivative-bounds.lisp` computes
`diskCap(Q,r)=coefficientMass(rescale(Q,max(1,r)))` and proves that it
bounds `Q` on the entire `r` disk. With
`D0=D(s,R,r,0,1)`, the fixed positive rational

```
C = 3+diskCap(D0,r)
```

bounds every local slope with `0<e<=1`; `C+2` bounds every derivative
model with `0<epsilon<=1`, independently of target and precision.

`polynomial-product.lisp` constructs product coefficient lists by Horner
convolution and proves exact multiplication on evaluation.
`polynomial-geometric-sum.lisp` constructs the polynomial
`S_n(Q)=1+Q+...+Q^(n-1)`, with `S_0=0`. If `disk(Q(z),q)` and
`q<1`, its inverse error is at most `q^n/(1-q)`; for `q=1/2`,
the sum itself has cap `4`. These are finite inversion tools. The residual
disk and actual inverse and quotient models are constructed below.
The normalized extension at one and uniform normalized polynomial
models are proved below; general factor models remain required.

### Generated nonzero neighborhoods and actual quotient models

`polynomial-disk-increments.lisp` bounds polynomial variation using the
coefficient mass of the divided difference. Given an accepted coarse
Euler check, `euler-nonzero-neighborhood.lisp` sets

```
A = V(s,a), S = L1(A)>0, a<=S/16, 0<R<sigma,
P0 = uniformPolynomial(s,R,0,a),
L = diskIncrementCap(P0,R),
r = min(R/2, roundingPrecision(L,S/32)).
```

It proves `0<r<R`, `r<=1` and `L*r<=S/64`. Throughout `disk(z,r)`,
every value polynomial with error at most `a`, and every actual value
`V(s+z,e)` with `0<e<=a`, lies within `S/4` of `A`.
Both have squared-norm lower bound `S^2/16` and reciprocal cap `4/S`.
The actual shifted value has `L1>=S/2`, so the same request `a/2`
generates an accepted coarse check at every shifted center, with clearance
lower bound at least `S/8`.

`polynomial-inverse.lisp` constructs

```
Z = 1-P/A,
Q_n = (1/A)*(1+Z+...+Z^(n-1)).
```

The residual disk `|Z|<=1/2` implies `P!=0` and gives
`|1/P-Q_n|<=2*B*2^(-n)`, where `B` bounds `1/A`.
The computed count
`inverseCount(B,e)=resolventTruncationCount(1/2,e/(1+B))`
meets any positive error `e`; every such inverse polynomial has cap
`4*B`. These are actual coefficient constructors, with exact evaluation
identities.

`euler-uniform-inverse.lisp` generates the residual disk for the actual
Euler polynomials, taking `B=2/S` and `K=(4/S)^2`. For output error
`E>0`, it uses

```
eta = min(a,roundingPrecision(K,E)),
P = uniformPolynomial(s,R,target,eta),
I = Q_n(P), n = inverseCount(B,E/2).
```

For every `disk(z,r)` and `0<eV<=a`,

```
disk(1/V(s+z,eV)-I(z), E+K*eV/4),
disk(I(z),4*B).
```

`euler-uniform-log-derivative.lisp` then sets

```
C = 2+uniformDerivativeCap(s,R,r), T=4/S,
M = T+C, N = T+C*K/4,
delta = roundingPrecision(M,E),
Wpoly = derivativePolynomial(s,R,r,target,delta)
        * inversePolynomial(s,R,a,target,delta).
```

The product is a generated coefficient list, independent of `z`.
Its cap `4*B*C` is independent of target degree and output precision.
For every `disk(z,r)`, `0<rho<Re(s+z)` and `eW>0`,

```
disk(W(s+z,rho,a/2,eW)-Wpoly(z), E+eW).
```

Here `W` is the existing actual checked quotient evaluator. The proof
computes a positive auxiliary request bounded by `a`, one quarter of
the shifted check's clearance, and
`roundingPrecision(localQuotientCost+N,E)`. This auxiliary request may
depend on the point; the model polynomial and its cap do not.
The node comparison costs `M*delta+N*request`, the existing quotient
comparison adds `eW+localQuotientCost*request`, and the two rounding
budgets make their sum at most `E+eW`. For `eW<=1`, the actual quotient
also has fixed cap `4*B*C+2` throughout the neighborhood.

These results construct local reciprocal and quotient models from finite
coarse value checks. The normalized extension at one is constructed next.
General zeta factors, complete zero covers and the analytic interpretation
of the full Landau reduction remain required.

### The computed normalized value at one

`euler-log-polynomial-cauchy.lisp` compares quotient polynomials at
independent degrees and requests throughout the same computed disk,
with error `E1+E2`. `polynomial-cauchy-caps.lisp` constructs one finite
coefficient-cap test: if the cap fails, its first failed coefficient
computes a positive disk gap and hence a sufficient Cauchy sample count.
The boundary test then contradicts that failure.
`euler-log-coefficient-caps.lisp` generates every boundary sample for the
actual quotient polynomials and their differences. Their normalized
coefficients have caps `Cw` and `E1+E2`, respectively.

`polynomial-tail-stability.lisp` bounds the tail on a half disk and
preserves its evaluation under padding. For a quotient polynomial
`P(z)` on the computed physical disk of radius `r`, write
`Q(w)=P(r*w)`. `euler-log-divided-difference.lisp` constructs

```
H(z) = (1/r)*Eval(cdr(Q),z/r).
z*H(z) = P(z)-P(0).
```

This is a polynomial, including at zero. On `|z|<=r/2`, its cap is
`2*Cw/r`, and the difference of two such polynomials has cap
`2*(E1+E2)/r`. Both bounds are independent of their degrees.

The normalized construction fixes the proved anchor check
`(sigma,height,a)=(1,0,1/64)` and outer radius `1/2`. Set

```
r = neighborhoodRadius(1,0,1/2,1/64), 0<r<=1/4,
Cw = uniformLogCap(1,0,1/2,1/64),
G = 1+2/r, K = 4*G,
epsilon(E) = roundingPrecision(K,E).
```

Here `K*epsilon(E)<=E/2`.
`euler-removable-numerator.lisp` constructs the actual numerator
coefficient list

```
N_target,E(z) = 1+P_target,epsilon(E)(0)-H_target,epsilon(E)(z).
CN = 1+Cw+2*Cw/r.
```

Its cap is `CN`. `euler-removable-value.lisp` uses exact rational
division by `1+z` to define

```
R_target(z,E) = N_target,E(z)/(1+z),
R(z,E) = R_0(z,E).
```

On the entire `r/2` disk, including zero, the denominator is nonzero
with reciprocal cap `4`. The family has cap `4*CN` and satisfies

```
disk(R_target1(z,E1)-R_target2(z,E2), (E1+E2)/2).
```

This constructs the center value by the same uniform Cauchy bounds as
its neighbors.

`euler-log-polynomial-anchor.lisp` proves agreement of the quotient
models with every accepted coarse check and with the actual gamma name
at the anchor. `complex-normalized-extension.lisp` proves the exact
complex-anchor identity

```
(1+b-h)/(1+z)
 = 1/(1+z) - (v-(1+z)*b)/((1+z)*z)
    when z*h=v-b, z!=0, 1+z!=0.
```

Its transport bound and the actual gamma calibration compare the local
models with the existing normalized evaluator.
`euler-removable-agreement.lisp` refines both Cauchy names and removes
the auxiliary errors by an explicit disk gap. For `0<|z|<=r/2`, any
accepted local check `aLocal` and admissible coefficient radius `rho`,

```
disk(R_target(z,E)-F_old(1+z,rho,aLocal,eF), (E+eF)/2).
```

`euler-removable-extension.lisp` defines `F_extended` to use the
computed name `R(0,e)` at `s=1` and the existing evaluator elsewhere.
It proves rational output, Cauchy radius `(e1+e2)/2`, and independence
from the accepted coarse check. Its local model comparison is

```
disk(R_target(z,E)-F_extended(1+z,rho,aLocal,eF), (E+eF)/2),
```

now for every `|z|<=r/2`, including zero. On `sigma>3`, it preserves
the actual Mellin comparison `5*eI+eF/2`.

These are proved arithmetic Cauchy-name and uniform rational-model
results. Uniform normalized polynomial models are constructed next.
General zero-region factor and contour models, complete covers and
analytic interpretation remain required.

### Uniform polynomial models of the normalized evaluator

`linear-inverse-polynomials.lisp` constructs finite inverse polynomials
for `u+z`. For nonzero rational complex `u`, on
`|z|<=L1(u)/4`, the inverse residual has cap `1/2`.
The computed geometric truncation meets any positive error; every inverse
polynomial has cap `4*B(u)`, where `B(u)=2/L1(u)`.
`polynomial-subtraction.lisp` subtracts coefficient lists of unrelated
lengths with an exact evaluation identity.

Away from one, `euler-normalized-disk.lisp` starts with an accepted
Euler check at `a=(sigma,height)`, an outer radius `0<R<sigma`,
the generated quotient neighborhood `rw` and its fixed cap `Cw`.
It computes

```
r = min(rw,L1(a)/4,L1(a-1)/4),
M = 1+L1(a)+r, C = Cw+2*M,
Ts = 4/L1(a), Tp = 4/L1(a-1),
As = 4*B(a), Ap = 4*B(a-1),
Ki = 1+C*(Tp+As), Kt = Ts*Tp*(1+M),
K = As+C*As*Ap,
delta = roundingPrecision(Ki+Kt,E), (Ki+Kt)*delta<=E/2.
```

The radius is positive and every `a+z` in its disk avoids zero and one.
`normalized-local-polynomial.lisp` constructs the generic coefficient
list; `euler-normalized-polynomial.lisp` instantiates it as

```
gamma = lower(EulerBounds(delta)),
Wpoly = uniformLogPolynomial(a,R,anchorError,target,delta),
P(z) = Is(z) - (Wpoly(z)-gamma*(a+z))*Is(z)*Ip(z),
```

where `Is,Ip` are the affine inverse polynomials for `a+z,a-1+z`,
both at error `delta`. One list works on the entire disk, with cap `K`.
It agrees with `F_extended` at every accepted shifted check and
admissible local coefficient radius `rho`, independently of its request:

```
disk(P(z)-F_extended(a+z,rho,localAnchor,eF), (E+eF)/2).
```

At one, set `rRem=neighborhoodRadius(1,0,1/2,1/64)`.
`euler-removable-polynomial.lisp` multiplies the existing numerator
at error `E/2` by an affine inverse polynomial for `1+z`.
Its inverse request satisfies `CN*request<=E/4`.
On the removable disk of radius `rRem/2`, the resulting polynomial
has cap `8*CN` and the same comparison, including at `z=0`.

`euler-local-normalized-model.lisp` combines these constructors.
Its computed disk radius `rLocal` and cap `KLocal` use the removable
branch at one and the preceding branch elsewhere. It generates an
accepted shifted check at every point: request `1/128` in the removable
branch, otherwise half the base check's request. It proves

```
disk(P_target1,E1(z)-P_target2,E2(z), (E1+E2)/2),
disk(F_extended(a+z,rho,localAnchor,eF), 1+KLocal)  (0<eF<=1).
```

`euler-local-normalized-coefficients.lisp` generates every finite
Cauchy boundary sample for `P(rLocal*w)` and padded polynomial
differences. All normalized coefficients have cap `KLocal`; all
difference coefficients have cap `(E1+E2)/2`. These caps contain no
degree, extraction index or output request.

These are local arithmetic models at certified nonzero Euler points,
including the removable center. Canonical coefficients, local series and
overlap agreement are proved next. General zero-region factor models,
complete contour and zero covers, and analytic interpretation remain
required for the full Landau theorem.

### Canonical normalized coefficients and local series

On a generated local disk of radius `r=rLocal` and cap `K=KLocal`,
write `Q_target,E(w)=P_target,E(r*w)`.
`polynomial-capped-coefficients.lisp` reads bounded coefficients and
padded differences, with zero outside each finite list.
`euler-normalized-coefficient-values.lisp` defines

```
a_k(e) = coefficient(Q_k,e,k).
disk(a_k(e),K),
disk(a_k(e1)-a_k(e2),(e1+e2)/2).
```

Comparison with any independently chosen polynomial target and request
has the same half-sum error. `euler-normalized-physical-coefficients.lisp`
uses `delta=min(1,e*r^k)` and defines `A_k(e)=a_k(delta)/r^k`.
This is exactly coefficient `k` of the corresponding raw local polynomial.
Its cap is `K/r^k`, with Cauchy radius `(e1+e2)/2`.

`euler-normalized-series-coefficients.lisp` assembles the actual
finite coefficient list `a_0(eC),...,a_(N-1)(eC)`; denote its evaluation
by `S_N(w,eC)`. For `0<=h<1`, `|w|<=h`, set `G=1/(1-h)`.
`euler-normalized-inner-series.lisp` proves

```
disk(S_N(w,eC)-F_extended(a+r*w,rho,localAnchor,eF),
     G*eC/2 + K*G*h^N + eF/2).
```

Every accepted check at the physical point and every admissible local
coefficient radius are allowed. The polynomial comparison's auxiliary
error is removed using an explicit rational disk gap.
The computed series evaluator chooses

```
N = resolventTruncationCount(h,E/(4*K)),
eC = min(1,E*(1-h)/4),
S(a,h,w,E) = S_N(w,eC).
```

The constructor proves `G*eC<=E/4` and `K*G*h^N<=E/4`.
Consequently `disk(S-F_extended,(E+eF)/2)`; the series itself has
fixed cap `K*G`. Its Cauchy radius is `(E1+E2)/2` even when
the two requests use different inner radii, provided both contain `w`.
All statements include the removable center at one.

`euler-normalized-overlap.lisp` proves the same half-sum comparison
between independently constructed charts at a common physical point.
Both polynomial and series comparisons permit different centers, outer
radii and accepted coarse checks.

For `Re(a+r*w)>3`, `euler-normalized-mellin-series.lisp` proves

```
disk(S(a,h,w,E)-I(a+r*w,eI),E/2+5*eI).
```

Thus `eI=E/10` meets output error `E`. This compares actual
computed families. Generation of general zero-region factors, complete
contour and zero covers, and analytic interpretation remain required.

### Checked finite contour models

`complex-segments.lisp` proves that rational complex disks are convex.
For rational `0<=t<=1`, endpoint membership in the same disk implies
membership of `segment(left,right,t)=(1-t)*left+t*right`.

`euler-contour-patches.lisp` packages a local model as the finite record
`patch=[sigma,height,R,anchorError]`. Its checker requires the accepted
coarse Euler check and `0<R<sigma`. It computes the existing local
center, radius, cap and shifted-check request, including the removable
branch at one. An edge is `[left,right,patch]`; its finite checker
tests that both endpoints lie in the patch disk.

These checks cover every rational point of the whole segment. Every
such point has positive real part and an automatically accepted shifted
Euler check. `euler-contour-segment-models.lisp` constructs its coefficient
list by affine composition:

```
Pedge_target,E(t)
 = Ppatch_target,E((left-center)+(right-left)*t).
```

It proves exact evaluation, cap `Kpatch`, and comparison with the
actual normalized evaluator at radius `(E+eF)/2`. The model is one
polynomial across the entire segment. Independent targets and requests
have Cauchy radius `(E1+E2)/2` there.

`euler-contour-cover.lisp` checks a finite list of edge records and sets

```
B = 1 + sum_edges Kpatch.
```

For every valid edge index and rational segment parameter, coverage and
the generated local check are proved. `euler-contour-models.lisp`
constructs the full list of polynomial models, proves its exact length
and indexed access, and defines

```
s_i(t) = segment(left_i,right_i,t),
V_i(t,e) = F_extended(s_i(t),Re(s_i(t))/2,anchor(patch_i),e).
disk(Pedge_i,target,E(t),B),
disk(Pedge_i,target,E(t)-V_i(t,eF),(E+eF)/2),
disk(V_i(t,eF),B+1)  (0<eF<=1).
```

The general comparison also permits every independently accepted local
check and admissible coefficient radius. The shared cap `B` contains
no model target, precision or selected edge index.

`euler-contour-closed.lisp` checks a nonempty closed polygonal path:
adjacent endpoints agree, and the final endpoint equals the start.
The computed successor wraps the last edge to zero. At every cyclic join,

```
disk(Pedge_i,target1,E1(1)-Pedge_next,target2,E2(0),(E1+E2)/2),
disk(V_i(1,e1)-V_next(0,e2),(e1+e2)/2).
```

Thus the arithmetic coverage, constructed model family and join bounds
follow from finite endpoint and coarse-value checks on a supplied patch
assignment. General contour-cover generation from zero data, winding
and multiplicity interpretation, actual zero-region factor models and
the analytic interpretation of these covers remain required.

### Constructed circular covers

The six books from `unit-circle-charts.lisp` through
`euler-circle-grid.lisp` extend coverage to circular arcs. The argument
uses the actual rational rotation

```
rot(u) = ((4-u^2)/(4+u^2), 4*u/(4+u^2)).
```

It has exact squared norm one and Lipschitz bound
`disk(rot(u)-rot(v),abs(u-v))`. For every rational unit point
`p=(x,y)`, compute

```
sign = if x<0 then -1 else 1,
u = 2*sign*y/(1+sign*x).
```

The denominator is positive, `-2<=u<=2`, and
`sign*rot(u)=p`. Thus the two signed charts cover every rational
unit-circle point, including the point missed by either single chart.
Physical points are `circle(a,R,sign,u)=a+R*sign*rot(u)`.

An arc record is `[sign,left,right,patch]` with
`-2<=left<=right<=2`. Set

```
mid = (left+right)/2,
reach = R*(right-left)/2.
```

An accepted midpoint disk check with radius `rPatch-reach>=0`
proves patch membership throughout the arc. It generates the existing
shifted Euler checks at every rational parameter in the interval.
This uses the arc distance estimate; endpoint convexity alone would
cover only the chord.

`euler-circle-cover.lisp` checks one interval chain from -2 to 2 for
each sign and computes the first containing arc. Every rational unit
point gets a covering patch. In particular this covers
`rotation(degree)^sample` for every natural degree and sample, rather
than merely checking finitely many chosen points of a circle.

Let `Kpatch` be the fixed local normalized cap and set

```
B = 1 + sum_plus Kpatch + sum_minus Kpatch.
```

At each physical point, `euler-circle-models.lisp` constructs the
selected spatial polynomial and evaluates it at displacement from its
patch center. It proves

```
disk(P_target,E(a+R*p),B),
disk(P_target,E(a+R*p)-F_cover(a+R*p,e),(E+e)/2),
disk(F_cover(a+R*p,e),B+1)  (0<e<=1).
```

Here the polynomial coordinates are relative to the selected patch.
Composition with the rational chart parameter is not asserted to be a
polynomial. Independent model requests have half-sum Cauchy bounds.
Native values from independently accepted covers also agree with
half-sum error.

Finally, `euler-circle-grid.lisp` constructs the arc records and their
patches from `a,R,N,e0`, where `N>0`. In each signed chart,

```
u_k = -2+4*k/N,
mid_k = -2+(4*k+2)/N,
q_k = circle(a,R,sign,mid_k),
patch_k = [Re(q_k),Im(q_k),Re(q_k)/2,e0].
```

There are exactly N arcs per chart, with reach `2*R/N`. The finite
node checker asks only for the accepted coarse Euler value check at
`q_k` and the computed local radius inequality
`2*R/N<=rPatch_k`. The patch center equals its arc midpoint exactly.
Accepted checks at all N nodes of both charts therefore generate a
complete circular cover. No arc records or patch assignment are supplied
by the caller.

`lw-euler-circle-grid-cauchy-sample` composes this construction with
the native models: every Cauchy sample has an accepted shifted check and
native cap `B+1`. The shared cap depends on the fixed grid and coarse
request, independently of degree, sample index and fine request.

These theorems prove the construction conditional on its finite node
checks. Selecting suitable N and e0 from general zero data, winding and
multiplicity interpretation, and actual zero-region factor construction
remain required for the full reduction.

### Actual global polynomial quotient models

`euler-circle-clearance.lisp`, `euler-circle-global-polynomial.lisp`
and `euler-circle-global-quotient.lisp` construct a global rational
model on a covered circle. The numerator is the formal derivative of
the same polynomial used as denominator.

Let the circle have center `c`, radius `R>0`, and an accepted
two-chart cover. Every point has positive real part, so the leftmost
point proves `R<Re(c)`. Compute

```
T = (Re(c)+R)/2,             R<T<Re(c),
delta = (T-R)/2 > 0,
m = min(1, all shifted patch anchors) > 0.
```

The minimum is computed over the two finite arc lists. At each rational
unit point `u`, let `z=c+R*u` and let `a>=m` be its selected
shifted anchor. Its accepted coarse check gives

```
size = L1(V(z,a)) >= 16*a,
lower = size/4 >= 4*m.
```

Every native value request at most `lower/4` has squared norm at
least `m^2` and reciprocal cap `1/m`, uniformly on the circle.

For a natural target and positive model request `e`, construct

```
P = uniformEulerPolynomial(c,T,target,delta*e),
D = formalDerivative(P).
```

This exact derivative identity is proved. The existing uniform derivative
constructor supplies the coefficient list for D. At displacement `R*u`,

```
disk(P(R*u)-V(z,eV), delta*e+eV/4),
disk(D(R*u)-nativeFirstCoefficient(z,rho,eD), e+eD).
```

The derivative comparison permits every admissible local coefficient
radius rho. For `e<=1`, D has the fixed cap

```
M = 2+uniformDerivativeCap(c,T,R).
```

If `delta*e<=m`, compare P directly with the accepted coarse
value V(z,a). Its error is at most `delta*e+a/4<=5*a/4<=size/4`.
The proved anchor-clearance estimate then gives P squared norm at least
`m^2` and reciprocal cap `1/m`. This is a uniform bound on the
constructed denominator, with no supplied polynomial-nonvanishing
hypothesis.

Let W(z,eW) be the actual checked Euler logarithmic derivative, using
coefficient radius Re(z)/2 and the generated shifted anchor. Define

```
Q(R*u) = D(R*u)/P(R*u),
K = 1/m + delta*M/m^2.
```

Then

```
disk(Q(R*u),M/m),
disk(Q(R*u)-W(z,eW), K*e+eW).
```

A temporary native request contributes at most
`(1/m+M/(4*m^2))*margin`. The native Cauchy bound and computed
disk-gap refinement eliminate that auxiliary margin.

For any positive requested output error E, compute

```
e(E) = min(1, m/(1+delta), E/(2*(1+K))).
```

This request is positive, satisfies `delta*e(E)<=m`, and has
`K*e(E)<=E/2`. The resulting model has comparison error
`E/2+eW`; choosing `eW=E/2` meets E. Independent degrees and
requests E1,E2 have half-sum Cauchy radius. The actual W values have
fixed cap `2+M/m` for `0<eW<=1`.

The generated-grid constructor supplies both the coefficient list P and
every circular Cauchy sample of Q. Its identity theorem proves that all
these samples evaluate the formal derivative divided by that same P;
the polynomial and its request are independent of Cauchy degree and
sample index.

These are boundary models for the Euler logarithmic derivative.
Interior roots are permitted. Uniform boundary agreement between
meromorphic functions with different interior poles does not by itself
bound their Taylor coefficient difference. Pole-coefficient comparison,
complete zero covers, uniform root counts, multiplicities and the
analytic interpretation remain required for the full reduction.

### Finite winding, stable grid refinement and certified root search

The eight books from `complex-orientation.lisp` through
`polynomial-root-search.lisp` build the finite arithmetic needed for
root counting and refinement.

For rational complex points a,b, define
`det(a,b)=Re(a)*Im(b)-Im(a)*Re(b)`. The integer crossing function is

```
cross(a,b) =  1  if Im(a)<=0<Im(b) and det(a,b)>0,
            -1  if Im(b)<=0<Im(a) and det(a,b)<0,
             0  otherwise.
```

This fixes the convention at vertices on the positive real ray.
Crossings reverse sign when the edge is reversed. Their sum around a
closed polygon is an integer between minus and plus its vertex count.

`complex-orientation.lisp` proves that a disk with center h and radius
r satisfying `r^2<normSquare(h)` lies in the open half-plane
`dot(h,point)>0`. Determinant identities then prove that every triangle
in one such half-plane has index zero. An edge potential makes this
telescope over arbitrary finite polygons. The same applies to each
quadrilateral grid cell.

For a rectangular grid of complex values, let each cell traverse its
bottom edge, right edge, reversed top edge and reversed left edge.
`grid-index.lisp` proves

```
sum_cell cellIndex
 = bottomPathIndex - topPathIndex + rightColumnIndex - leftColumnIndex.
```

Every internal edge cancels exactly. The right-hand side defines the
computed boundary index.

The finite cell-variation checker bounds the three differences from each
bottom-left value to the other three cell values by epsilon. If bounded
search found no value in `disk(0,epsilon)`, every bottom-left anchor
would have squared norm greater than `epsilon^2`. Each cell would
then lie in a positive half-plane and have index zero. Boundary
cancellation contradicts a nonzero boundary index. The proved search
returns both grid indices and a value with magnitude at most epsilon.

`polynomial-lipschitz.lisp` supplies the variation bound for actual
finite polynomials. For a disk of radius B, compute

```
L([],B) = 0,
L(a::tail,B) = polynomialDiskCap(tail,B) + B*L(tail,B).
```

For `z,w` in that disk with `disk(z-w,h)`, the actual polynomial
values satisfy `disk(P(z)-P(w),h*L(P,B))`. This follows by finite
Horner identities and induction, with no derivative or Lipschitz
hypothesis supplied by the caller.

For a square with rational lower-left corner a and side s>0, and a
positive requested error epsilon, compute

```
B = 1 + L1(a) + 2*s,
L = L(coefficients,B),
N = 1 + ceil(4*s*(1+L)/epsilon),
h = s/N.
```

The grid has exactly N+1 rows and columns. Its vertices are
`a+h*(column+i*row)`, with both indices from 0 to N. They lie inside
the square and the disk of radius B. Adjacent and diagonal cell
displacements have radius at most 2h, and the computed count proves
`2*h*L<=epsilon`. Thus every finite cell-variation check is generated.

`lw-polynomial-root-search-witness` proves that, when the boundary
index of this computed polynomial-value grid is nonzero, bounded search
returns a rational complex point q satisfying

```
Re(a)<=Re(q)<=Re(a)+s,
Im(a)<=Im(q)<=Im(a)+s,
disk(P(q),epsilon).
```

The address, mesh and polynomial evaluations are actual terminating
rational computations. Search soundness also holds independently of the
index condition.

This is an approximate-root theorem from a finite nonzero-index
certificate. It does not claim that every chosen square has such an
index, that an exact root is rational, or that the index already counts
analytic zeros. The stronger fixed-certificate theorem below removes the
error-dependent index hypothesis. General nonzero-index construction,
complete root covers, multiplicities and their analytic interpretation
remain required.

Four further books prove finite index stability. `polygon-refinement.lisp`
replaces any checked edge by a proper finite chain in one open half-plane.
The edge potential proves that the chain has the same crossing contribution;
concatenation preserves both endpoints and the closed polygon index. A metric
checker generates these half-planes from an anchor outside `disk(0,epsilon)`
and rational distance bounds to all inserted vertices.

`polygon-homotopy.lisp` closes both polygons explicitly. Every cyclic pair
of corresponding edges forms a quadrilateral. Checked nonzero collars put
each quadrilateral in one half-plane, so its index is zero. Exact strip
cancellation proves that the two polygon indices agree.

For actual polynomial values, `polynomial-edge-refinement.lisp` computes
`E=radius*L(coefficients,bound)`. Its finite edge check requires both domain
endpoints in the disk of radius `bound`, their difference in the disk of
radius `radius`, and `E^2<normSquare(P(left))`. Segment convexity and the
proved polynomial variation bound put every rational segment sample in one
positive half-plane. For every positive subdivision count N, the generated
N-1 interior samples retain exactly the original edge crossing contribution.
No new clearance check is needed as N changes.

`lw-polynomial-path-refinement-index` assembles these samples along all
consecutive pairs of a finite path. Its polygon index is unchanged; the
implicit last-to-first edge stays the same. Repeating the starting domain
point as the final vertex refines that closing segment too. These theorems
now connect to the actual square-grid boundary. `polygon-paths.lisp`
proves concatenation and reversal. `grid-perimeter.lisp` constructs

```
bottomRow ++ rightColumn ++ reverse(topRow) ++ reverse(leftColumn).
```

Keeping duplicate corners makes every join and the final closing edge a
self edge. Its polygon index is exactly the existing four-path grid index.
For width w and height H the perimeter has 2*(w+H) vertices; the square
has 4*(N+1). `polynomial-grid-perimeter.lisp` constructs domain vertices
using the identity polynomial grid and proves that evaluation of P maps
those vertices exactly onto the actual value-grid perimeter.

`polynomial-line-sampling.lisp` supplies exact uniform segment samples,
crossing-sum splitting and endpoint identities. Rational affine
reparameterization in `polynomial-line-refinement.lisp` proves that
subdividing every accepted coarse edge K times leaves its crossing sum
unchanged. `polynomial-grid-columns.lisp` identifies the actual top row
and both side columns. These combine in
`lw-polynomial-square-refinement-index`: the actual boundary indices at
counts M and M*K agree whenever the finite coarse boundary check passes.

The check `lw-polynomial-square-boundary-check` uses

```
B = 1 + L1(a) + 2*s,
h = s/M,
E = h*L(coefficients,B).
```

For each of the four sides and every coarse subsegment, it checks both
domain endpoints in the disk of radius B, their difference in the disk
of radius h, and `E^2<normSquare(P(start))`. All evaluations and checks
are finite rational computations. The check and the coarse index are
independent of the later root-search error.

Given a valid polynomial, rational lower-left corner a, side s>0,
positive coarse count M, an accepted coarse boundary check and nonzero
coarse grid index, compute for every rational epsilon>0

```
N0 = 1 + ceil(4*s*(1+L(coefficients,B))/epsilon),
N = M*N0.
```

The fine mesh retains `2*(s/N)*L<=epsilon` and inherits the coarse
nonzero index. `lw-polynomial-certified-root-search-witness` therefore
returns a computed rational point q in the closed square with
`disk(P(q),epsilon)`. The fine nonzero-index condition is proved from
one fixed certificate. Constructing such certificates from general zero
data, producing zero-counted covers and interpreting multiplicities
remain required.

### Computed small-value covers and native Euler clearance

The eight books from `square-cells.lisp` through
`euler-positive-square-cover.lisp` construct complete finite enclosures
of rational small-value regions. No nonzero-index hypothesis is needed
to construct these covers.

For a rational square with lower-left corner a, side s>0 and count N,
a bounded coordinate search computes the containing cell of every rational
point, including the top and right boundary. With

```
h = s/N,
B = 1 + L1(a) + 2*s,
v = 2*h*L(coefficients,B),
```

every point of a cell differs from its lower-left grid vertex by at most
2h. The proved polynomial variation bound therefore has radius v.
Retain a cell exactly when its anchor value lies in
`disk(0,epsilon+v)`. The resulting list has at most N^2 addresses,
all in range. Its geometry is defined directly from those addresses.

`lw-polynomial-sublevel-cover-complete` and the corresponding value
bound prove, for rational points in the closed square,

```
{ |P| <= epsilon }  subset  union(retained cells)
                      subset  { |P| <= epsilon + 2*v }.
```

Every discarded cell excludes values in `disk(0,epsilon)`.
For requested spatial width w>0 and value error epsilon>0, compute

```
M = 1 + ceil(s/w),
N0 = 1 + ceil(4*s*(1+L(coefficients,B))/epsilon),
N = M*N0.
```

The mesh satisfies 0<h<=w and 0<=v<=epsilon. Thus the resolved cover
lies between the epsilon and 3*epsilon sublevel sets. An empty cover
certifies absence of all epsilon-small rational values. A fixed accepted
nonzero boundary certificate guarantees the resolved cover is nonempty,
using the already proved approximate-root witness.

For native Euler values, `euler-square-cover.lisp` first uses a local
square inside a computed disk. It constructs an actual Euler polynomial
with error epsilon/4 and applies the resolved cover above. At every fine
native request 0<eV<=epsilon, all samples with magnitude at most
epsilon/2 are covered. At any covered point the native sample has bound

```
13*epsilon/4 + eV/4.
```

Outside the cover, the request epsilon/64 generates an accepted Euler
value-clearance check with lower bound epsilon/8. Every request at most
epsilon/32 has squared denominator norm at least (epsilon/8)^2 and
reciprocal cap 8/epsilon. The existing neighborhood constructor then
computes positive regular-chart radii and accepted shifted checks.

The construction applies to every closed square strictly inside Re(s)>0.
For x=Re(a)>0, `positive-square-disk.lisp` computes

```
A = x + s + 1 + s^2/x,
H = Im(a) + s/2,
R = A - x/2.
```

It proves 0<R<A and that every square point z has `disk(z-(A+i*H),R)`.
`euler-positive-square-cover.lisp` builds the Euler polynomial on that
disk and translates its actual coefficient list to physical coordinates.
The cover therefore evaluates the actual native family V(Re(z),Im(z),eV)
throughout any positive square, with the same completeness, value bounds,
generated clearance checks and uniform reciprocal cap.

These are arithmetic coverage and exclusion theorems for rational
evaluators. The covers do not yet carry analytic zero counts, certified
multiplicities or isolated clusters. Those interpretations and the
uniform pole/factor models required by the full Landau theorem remain
open.

### Retained indices and circle clearance from computed covers

The eight books from `polynomial-cell-index.lisp` through
`euler-square-circles.lisp` attach signed finite indices and native
boundary clearance to these computed covers.

For each address (row,column), define its cell index as the native
quadrilateral ray index of the four actual polynomial grid values, in
counterclockwise domain order. Explicit row and cell sums agree with the
existing native grid-cell sum. An inactive cell has all four values in a
common positive half-plane, hence index zero. Therefore

```
sum(cellIndex(address), address in sublevelCover(P,a,s,N,epsilon))
    = gridBoundaryIndex(polynomialGrid(P,a,s,N)).
```

`lw-polynomial-sublevel-cover-index-conservation` proves this for every
valid polynomial, rational square, positive count and positive epsilon.
It needs neither an accepted coarse certificate nor a nonzero index.

The bounded `lw-polynomial-sublevel-index-address` search scans the
actual retained list for the first nonzero cell index. A nonzero outer
index guarantees an address in range, membership in the retained cover,
nonzero cell index and anchor-value bound epsilon+variation.
This is a statement about a signed sum; it does not assert positivity
or analytic zero multiplicity.

`lw-polynomial-indexed-cover-count` multiplies the resolved count by a
fixed positive coarse count C. With one accepted boundary certificate
at C, the fine grid and retained cover inherit the coarse boundary index
for all requested width w>0 and epsilon>0. The resulting mesh still has
h<=w and variation<=epsilon. The computed nonzero-index address has
anchor value at most 2*epsilon when the coarse index is nonzero.
The same retained-index conservation applies to the actual translated
Euler polynomial and its computed positive-square cover. Every discarded
Euler cell generates the native value checks, local regular charts and
uniform reciprocal bounds above.

`lw-square-cell-box` represents a cell as
`(xmin xmax ymin ymax)`; membership is exactly the existing closed-cell
predicate for valid geometry. Mapping the actual address list to boxes
therefore preserves its point set, including shared edges and corners.
The finite `lw-boxes-avoid-circlep` check accepts each box only when its
entire squared-distance enclosure lies strictly below or strictly above
the requested squared radius. All accepted boxes miss that circle.

`lw-euler-square-circle-check(a,s,w,epsilon,center,r)` combines:

- a positive rational square and positive width and error;
- coordinate bounds placing the entire radius-r disk inside the square;
- that distance check on the boxes of the actual computed Euler cover.

For every rational point z with exact squared distance r^2 from center,
`lw-euler-square-circle-uncovered` proves z lies outside the retained
cover. Consequently, uniformly around the circle,

```
acceptedValueCheck(z,epsilon/64),
valueClearanceLower(z,epsilon/64) >= epsilon/8,
0<eV<=epsilon/32  ==>  normSquared(V(z,eV)) >= (epsilon/8)^2,
                      disk(1/V(z,eV),8/epsilon).
```

These conclusions hold at every rational chart parameter and at
`lw-cauchy-circle-point(center,r,degree,sample)` for all natural degree
and sample. Neither the cover nor its clearance bound depends on those
indices or on the fine request. Positive regular neighborhoods and
accepted shifted checks are generated at the circle points as well.

The circle check is a finite geometric certificate. This does not yet
prove that a suitable isolating circle can always be found, interpret the
finite signed indices as analytic zero counts, or construct the required
interior pole models. Those obligations remain part of the full reduction.

### Stable native Euler indices from one coarse polygon certificate

The eight books from `polygon-perturbation.lisp` through
`euler-native-polygon-index.lisp` fix a signed finite Euler sample index
across model degrees and fine requests on a fixed sampled contour.

`lw-euler-positive-square-model(a,s,target,E)` uses the actual Euler
uniform polynomial on the computed enclosing disk and translates its
coefficients to physical coordinates. At target zero it is exactly the
polynomial already used by the positive-square cover. For every square
point z and independent natural targets, the proved comparisons are

```
disk(P_target,E(z) - V(z,eV), E/4 + eV/4),
disk(P_left(z) - P_right(z), (E_left+E_right)/4).
```

No coefficient list or functional comparison is supplied by the caller.

For a finite nonempty rational point list inside the positive square,
`lw-euler-polygon-index-check(a,s,points,baseTarget,baseError,step,eta)`
checks positive eta, 0<baseError<=eta, step>=0 and the following finite
conditions. Let P0 be the actual base polynomial, let
B=1+L1(a)+2*s, and let L be its computed coefficient Lipschitz cap.

- Every adjacent domain pair, including last-to-first, differs by at most step.
- step*L<=eta/4.
- Every sampled P0 value lies outside the closed eta disk.

The polygon perturbation theorem combines a pointwise difference bound
with a base edge budget. Applied here, it proves

```
0<E<=eta, target natural
  ==> polygonIndex(P_target,E(points)) = polygonIndex(P0(points)).
```

The actual native evaluator is also mapped over the same domain list.
`lw-euler-native-polygon-index-stable` proves the exact integer identity

```
0<eV<=eta
  ==> polygonIndex(V(points,eV)) = polygonIndex(P0(points)).
```

Thus independent native requests and polynomial models all have the same
finite sample index. The native Euler family is evaluated directly; it
is not replaced by an assumed model identity.

The coefficient budget controls whole segments as well. For every
natural edge index less than the original point-list length,
`lw-euler-polygon-edge-point` selects that edge in the explicitly closed
list and evaluates any rational parameter 0<=t<=1. Square convexity
keeps the entire segment in the positive square. The base polynomial
varies by at most eta/4 from its left endpoint. Every fine polynomial
with 0<E<=eta therefore lies within 3*eta/4 of that base value and in
its open positive half-plane, independently of its target degree.

At every such segment point, native requests 0<eV<=eta lie outside the
eta/4 disk. Consequently the generated checks and denominator bounds are

```
acceptedValueCheck(z,eta/64),
valueClearanceLower(z,eta/64) >= eta/16,
0<request<=eta/64 ==> normSquared(V(z,request)) >= (eta/16)^2,
                     disk(1/V(z,request),16/eta).
```

These cover the closing edge as well as every ordinary edge, with caps
fixed across model degree, edge parameter and fine precision.

`lw-euler-square-index-check` applies the same finite certificate to
the canonical square boundary at a fixed positive count N. The native
sample index equals the actual model grid-boundary index for all
admissible targets and requests. For every epsilon>0, the retained
sublevel cover of any such model carries that same signed index.
A nonzero coarse index gives a computed retained nonzero-index address.
Its anchor-value bound remains epsilon+cellVariation; this theorem does
not add a resolution bound at the fixed N.

The following section extends these results to generated integer
subdivisions and canonical model grids at coarse-mesh multiples.
Nonnegative analytic zero-count and multiplicity interpretations, cluster
handling and compatible interior pole models remain open.

### Native mesh refinement and resolved indexed Euler covers

The eight books from `polygon-slices.lisp` through
`euler-native-indexed-cover.lisp` connect the fixed coarse certificate to
subdivided native contours and adaptive square covers.

On each coarse edge, every native sample at request 0<eV<=eta lies within
3*eta/4 of the actual base polynomial's left value. That base value is
outside the eta disk, so all such samples lie in one open positive
half-plane. Every positive integer subdivision has the same crossing
contribution as its actual native endpoint values.

The block constructor generates all samples and base anchors and proves
the existing finite refinement checker accepts them. Explicit closure
includes the last-to-first edge. For every positive integer factor,

```
index(nativeRefinedPolygon(points,factor,eV))
    = index(nativeValues(points,eV))
    = index(P0(points)).
```

Independent factors and requests 0<eV<=eta give the same integer.
`lw-euler-native-refined-polygon-domain` identifies the constructed list
exactly with native Euler values on the actual subdivided domain polygon,
using the existing identity-polynomial path refinement. This is not a
caller-supplied list or refinement check.

For canonical square grids, fix a positive coarse count C and use the
existing square certificate with its step set to h=s/C. The perimeter
avoidance check supplies clearance on each of the four forward side
lists. A coefficient-controlled disk around each coarse left value
contains every fine model sample on that segment. Exact side crossing
sums therefore give, for every positive integer factor and natural target,

```
0<E<=eta ==>
  gridIndex(P_target,E, C*factor)
    = gridIndex(P_target,E, C)
    = nativeIndex(squareBoundary(C),baseError).
```

The coarse model, clearance, count and coefficient budget stay fixed.
The proof does not require a boundary check for the fine model, a fine
coefficient budget supplied by the caller, or an error-dependent
nonzero-index premise.

For requested width w>0 and error epsilon>0, compute

```
E = min(eta,epsilon),
P = eulerPositiveSquareModel(a,s,target,E),
N = C * polynomialResolvedCoverCount(P,a,s,w,epsilon).
```

`lw-euler-native-indexed-cover-count-data` proves N is positive,
0<s/N<=w and 0<=cellVariation(P,N)<=epsilon. The constructors use this
actual polynomial and mesh to enumerate retained addresses and to search
for a nonzero-index cell. Their finite bounds and exact conservation are

```
retainedCells <= N^2,
sum(retained cell indices) = nativeIndex(squareBoundary(C),baseError).
```

This holds for every target and every requested width and error, even
though the model coefficients, degree, mesh and retained list vary.
If the fixed native index is nonzero, the computed address is retained,
in range, has nonzero cell index, and its model anchor value is at most
2*epsilon.

The cover also has its native value meaning. For rational points in the
square and every 0<eV<=epsilon, all native samples with magnitude at most
epsilon/2 are covered. At every covered point and any positive eV,

```
disk(V(z,eV),13*epsilon/4+eV/4).
```

Uncovered square points exclude epsilon/2-small native samples at all
requests at most epsilon. They generate an accepted value check at
epsilon/64, lower bound epsilon/8, and reciprocal cap 8/epsilon for every
0<request<=epsilon/32. The existing neighborhood constructor can use these
accepted checks to generate regular charts.

These are signed finite indices and complete rational small-value covers.
Analytic nonnegative zero counts, multiplicity interpretation, general
cluster and pole/factor coefficient models, and the full arithmetic
interpretation of windowed Landau remain required.

### Finite winding multiplication and generated product checks

The ten books from `ray-positive-scales` through
`polygon-product-additivity` prove multiplication laws for the existing
integer ray-crossing index. The edge-safety predicate requires complex
endpoints and either a nonzero determinant or a positive dot product.
It includes positive collinear edges and excludes edges through zero.

For a triangle with three safe edges, its index is 1 when all three
cyclic determinants are positive, -1 when all are negative, and 0
otherwise. Multiplying all vertices by a nonzero rational complex h
scales determinants and dot products by the positive quantity
`normSquare(h)`, so it preserves this triangle index.

For any finite list of nonzero rational complex points, compute

```
t = 1 + sum f(x,y),   f(x,y)=0 if x=0, otherwise abs(y/x),
h0 = (1,t).
```

ACL2 proves `det(h0,z)!=0` at every vertex. The zero-real-coordinate
branch is explicit in the executable constructor. Exact fan
triangulation then proves that multiplying any safe closed polygon by
any nonzero rational complex constant preserves its winding number.

For two equally long closed paths A and B, with the final vertex equal
to the first, the pointwise product has vertices `B_i*A_i`. The
product-grid checker tests common positive half-planes on its triangular
cells. Triangle and strip cancellation identify the diagonal crossing
sum with the bottom row followed by the right column. Constant-factor
invariance makes the winding of the pointwise product equal to the sum
of the two input winding numbers.

The checks are generated from global rational budgets. Suppose

```
0 < rA <= abs(A_i) <= RA,    0 < rB <= abs(B_i) <= RB,
delta = rA*rB / [4*(1+RA+RB)],
abs(A_(i+1)-A_i) <= delta,  abs(B_(i+1)-B_i) <= delta.
```

The constructor proves delta is positive and
`delta*(RA+RB)<rA*rB`. Every product-grid corner lies within
`delta*(RA+RB)` of its lower-left product, whose modulus is at least
`rA*rB`. This gives the required common positive half-planes. The
same budget generates safe input paths and proves winding additivity;
no half-plane or index-equality hypothesis is supplied to
`lw-ray-product-index-at-computed-step`.

Later sections combine these finite winding laws with complete
approximate factorization to prove nonnegative checked unit-square
polynomial indices. Native analytic multiplicity interpretation remains
a separate obligation.

### Constructed monomial indices and leading-term radius

The twelve books from `complex-outer-powers` through
`polynomial-leading-radius` connect finite winding multiplication to
actual polynomial coefficients and the canonical square grid.

For complex z, `normSquare(z^k)=normSquare(z)^k`. On the radius-two
disk, an input difference bounded by e gives a power difference bounded
by `4^k*e`. A common path in the annulus `1<=abs(z)<=2` therefore has
all power samples through degree d in the annulus `1<=abs(z^k)<=2^d`.
Set

```
U = 2^d,
delta = 1/[4*(1+2*U)],
e = delta/(1+4^d),
N = 4*(1+ceil(1/e)).
```

All these quantities are computed rationally. The canonical unit-square
boundary has step `2/N<=e`, repeated endpoint joins, and annulus bounds
1 and 2. A fixed, computed certificate at mesh 4 gives its index one
at every multiple mesh. The product winding laws prove that sampling
`z^d` on this boundary has index d. Multiplication by any nonzero
rational complex leading coefficient preserves that index.

The constructor `lw-polynomial-square-line-boundary` samples the four
sides directly. It equals the existing mapped canonical perimeter, so
its proofs and execution need no full grid just to construct a boundary.
The actual monomial coefficient constructor, its polynomial evaluator,
and the canonical grid all have the same computed degree index.

For a nonconstant coefficient list P with nonzero final coefficient a,
write L for its lower coefficient list, `d=len(L)>=1`, and
`M=sum L1(L_i)`. Exact polynomial concatenation proves

```
P(w) = L(w) + a*w^d.
```

For a coefficient list of length at most j+1 and `abs(w)<=r`, r>=1,
the evaluator has bound `coefficientMass*r^j`. In particular,
`abs(L(w))<=M*r^(d-1)`; retaining d-1 is necessary for outer dominance.

The positive rational lower bound and radius are computed by

```
n = normSquare(a),
ell = n/(1+n),          0 < ell <= 1, ell^2 <= n,
R = 1 + 16*M*2^d/ell.
```

The executable radius constructor handles a zero leading coefficient
explicitly; the comparison theorem requires that coefficient to be
nonzero. For every rational complex w with `abs(w)<=2*R`, ACL2 proves

```
abs(P(w)-a*w^d) <= ell*R^d/16.
```

### Generated outer index and rational approximate roots

The leading comparison now generates the finite homotopy checks.
Write `A=ell*R^d`, `B=L1(a)*R^d` and
`F=R^d*a`. For any closed path in the unit-to-two annulus, the leading
path `F*z^d` has lower norm `A` and adjacent-step cap
`B*4^d*error`. Its pointwise distance from `Q(z)=P(R*z)` is at most
`A/16`. A leading-path step at most `A/16` therefore generates a
homotopy collar of radius `A/8<A`.

`lw-polynomial-outer-path-index` proves that the index of `Q` on such
a path is `d` times the domain path's index, when its step also meets
the previously computed power budget. All these bounds come from the
coefficient list. The positive step target is

```
tau = min(powerStepBudget(d), A / (16*(1+B)*4^d)).
u   = 1 + ceil(1/tau).
```

The unit-square mesh with `4*u` subdivisions has index one and step at
most `tau`. Every sufficiently fine multiple mesh has the same generated
polynomial index `d`. Denominator-zero branches keep the scalar constructors
executable outside the valid-input domain.

For `epsilon>0`, let `v` be the existing coefficient-based
`lw-polynomial-root-count(Q,(-1,-1),2,epsilon)`. The common search mesh is

```
N = 4*(u+v).
```

`polynomial-global-root-mesh.lisp` proves that its actual polynomial
grid has boundary index `d` and every small-cell variation check.
For a proper rational-complex coefficient list of length at least two
with nonzero final coefficient, `lw-polynomial-approximate-root`
therefore proves, for every positive rational `epsilon`:

```
address = globalRootAddress(coefficients, epsilon) is a pair;
w       = globalRootPoint(coefficients, epsilon) is rational-complex;
abs(w) <= 2*R;
abs(P(w)) <= epsilon.
```

No boundary-index, root or cell-witness certificate is supplied.
`polynomial-streaming-search.lisp` generates rows on demand and proves
its `-fast` address and point equal to those of the full finite grid.
It can stop after the first successful row; the mathematical proof
still uses the same complete grid.

Exact executions with normal ACL2 guard checking gave outer index one
for `P(z)=z+1` at `R=65`, count `524`, and index two for
`P(z)=z^2+1` at `R=129`, count `2452`. For `P(z)=z` and
`epsilon=1/2`, the computed search count is `1160`, the address is
`(290 . 580)`, and the returned point is `(0 . -1/2)`; both the
polynomial-error and radius checks evaluate to true.

### Complete rational approximate factorization

`polynomial-division-leading.lisp` proves that synthetic division preserves
the nonzero final coefficient and reduces the represented degree by one.
Its exact identity is

```
P(z) = P(r) + (z-r)*Q(z),
Q    = polynomialDividedDifference(P,r).
```

For a nonempty coefficient list with nonzero final coefficient, disk
bound `B>=0` and tolerance `epsilon>0`,
`lw-polynomial-factor-roots` computes the factors recursively:

```
r            = globalRootPointFast(P, epsilon/2);
nextEpsilon  = epsilon / (2*(1+B+2*leadingRadius(P)));
remaining    = factorRoots(Q, B, nextEpsilon).
```

A singleton list ends the recursion. The root bound `abs(r)<=2*R`
makes `abs(z-r)<=B+2*R` on the disk. The generated budget proves

```
epsilon/2 + (B+2*R)*nextEpsilon <= epsilon.
```

The recursion terminates by coefficient-list length. It returns exactly
`degree(P)` rational-complex roots, without a supplied root certificate.
`lw-polynomial-approximate-factorization` proves that the single product
model `a*product(z-r_i)` has error at most `epsilon` at **every rational
point** `abs(z)<=B`. The root list depends on the coefficients, disk bound
and tolerance; it is independent of the evaluation point.

`lw-polynomial-trim` removes trailing zero coefficients while preserving
every polynomial value, including at arbitrary nonnegative offsets.
`lw-polynomial-normalized-approximate-factorization` extends the result to
all proper rational-complex coefficient lists. Its factor count is the
trimmed degree; constants and the zero polynomial have empty root lists.

Normal-guard executions constructed two rational factors for `z^2`
with `B=1` and `epsilon=2048`, checked their errors at zero and one,
and evaluated the constant base case exactly. A padded representation of
`z` trimmed to degree one and returned the root `-i` at tolerance two.
An all-zero list trimmed to the empty list and its product model was
exactly zero. These are execution checks; the certified theorems give
the uniform error bound at every requested positive rational tolerance.

### Linear-factor winding and generated clearance

`ray-axis-crossings.lisp` gives the exact vertical-edge potential

```
cross((x,y1),(x,y2)) = if x>0 then I(y2>0)-I(y1>0) else 0.
```

Horizontal crossings vanish. Their path sums telescope, and translation
preserves the canonical square's fixed coordinates and endpoint joins.
For every rational-complex root `r` and every positive mesh count,
`lw-unit-square-translated-boundary-index` proves

```
index(z-r on square) =
  if -1 <= Re(r) < 1 and -1 <= Im(r) < 1 then 1 else 0.
```

The raw finite index follows the half-open convention even for boundary
roots. It is not an analytic zero count at a boundary zero.

The rational square radius `M(z)=max(abs(Re(z)),abs(Im(z)))` satisfies

```
abs(M(z)-M(r))^2 <= normSquare(z-r).
```

Every canonical boundary sample has `M(z)=1`. Define

```
gap(r) = abs(1-M(r));
cap(r) = 2+L1(r).
```

`unit-square-clearance.lisp` proves that the translated boundary lies
in this annulus and that `gap(r)>0` exactly when the rational root is
off the unit-square boundary. Translation preserves the adjacent-step
bound. For positive gap, `unit-square-linear-bounds.lisp` computes

```
N(r) = 4*(1+ceil(2/gap(r))).
```

The mesh step is at most `gap/2`, so every polygon edge is safe.
Multiplication by any nonzero rational-complex leading coefficient
preserves its zero-or-one index. No separate edge or safety certificate
is supplied.

Exact normal-guard executions gave:

| Root | Gap | Computed count | Index, also after multiplication by -3+4i |
|---|---|---|---|
| `0` | `1` | `12` | `1` |
| `3/2` | `1/2` | `20` | `0` |
| `1+2i` | `1` | `12` | `0` |

All three annulus and safety checks evaluated to true. Boundary examples
verified the raw convention: the left and bottom midpoints and the
bottom-left corner have index one; the right and top midpoints and the
top-right corner have index zero. Their gap is zero, so the safe-mesh
theorem does not apply.

### Common product meshes and nonnegative polynomial indices

For a complete factor family off the unit-square boundary and nonzero
leading coefficient `a`, the product budgets are recursive. At the empty
tail they are `L=nonzeroLower(a)`, `U=L1(a)`, `H=0` and `T=1`.
For the next root `r`, use the already computed tail quantities:

```
L = gap(r)*Ltail;
U = cap(r)*Utail;
H = cap(r)*Htail + Utail;
D = productStepBudget(gap(r),cap(r),Ltail,Utail);
T = min(Ttail, D/(1+Htail)).
```

All quantities are rational; `L,T>0` and `U,H>=0`. Actual product
values satisfy the annulus `L..U`, and their adjacent-step cap is
`H*domainStep`. The target `T` controls every partial product on one
mesh. `lw-polynomial-factor-square-index` proves, for any positive count
with `2/count<=T`,

```
index(a*product(z-r_i)) = sum(unitSquareRootIndex(r_i)).
```

The computed count is `4*(1+ceil(1/T))`. Its index is nonnegative and
at most the number of factors; repeated roots are allowed.

The original polynomial needs no separate factor-clearance hypothesis.
`polynomial-edge-clearance.lisp` extracts positive rational slack from
each existing edge certificate. Minima give line and square clearances.
A computed ceiling-based cell and local parameter cover every rational
point of each coarse segment, including its endpoints. Thus a coarse
unit-square boundary certificate computes `gamma>0` such that

```
abs(P(z)) > gamma
```

at every rational boundary point. The complete factorization at disk
bound two and error `epsilon=gamma/4` gives one model `F` there.
A finite member search and the exact vanishing of a product at any member
root prove that every generated root is off the boundary: a boundary
member would give `F(r)=0` and contradict the polynomial clearance.
The product itself stays outside the disk of radius `2*epsilon`.

For this generated family, set

```
S = min(T, epsilon/(1+H));
refinementFactor = 4*(1+ceil(1/S));
N = coarse*refinementFactor.
```

Both the factor winding budget and the homotopy step budget hold on
this common refinement. The product-to-polynomial perturbation has
radius `epsilon`, the product step is at most `epsilon`, and the
positive collar excludes radius `2*epsilon`. Finite homotopy and the
existing stable coarse-refinement theorem prove

```
coarseGridIndex(P) = sum(unitSquareRootIndex(generatedRoots));
0 <= coarseGridIndex(P) <= degree(trim(P)).
```

The exact theorem is `lw-polynomial-checked-square-factor-count`;
`lw-polynomial-checked-square-index-nonnegative` exports the bounds.
Its inputs are a proper rational-complex coefficient list, a positive
coarse count and the existing accepted unit-square boundary checker.
No root list, positive-index assumption, uniform boundary margin,
factor-clearance check or fine-mesh certificate is supplied.

Normal-guard executions checked two product families: roots `(0,2)`
with leading coefficient one gave count `452` and index `1`; repeated
roots `(0,0)` with leading coefficient `-3+4i` gave count `2268`
and index `2`. Both annulus and step checks passed. The complete
coarse-certificate construction for `P=1`, coarse count one, gave
clearance `1/8`, error `1/32`, refined count `132`, empty factors
and equal coarse, fine-polynomial and product indices zero; its
pointwise comparison and collar checks passed.

These are finite polynomial winding counts. The following transport
extends them to arbitrary checked rational squares and canonical native
Euler square contours. Analytic zero counts, multiplicity interpretation
and compatible pole coefficients remain required for the full reduction.

### Rational-square transport and native nonnegative indices

For a proper rational-complex coefficient list `P`, rational complex
anchor `a`, positive rational side `s` and positive coarse count `C`,
assume the existing physical-square polynomial boundary checker accepts.
The new constructors first trim trailing zeros, then set

```
center = a + (s/2)*(1+i);
Q(z) = trim(P)(center + (s/2)*z);
gamma = polynomialSquareClearance(P,a,s,C);
factor = polynomialRootCount(Q,(-1,-1),2,gamma);
N = C*factor.
```

The factor constructor returns one when gamma is nonpositive; acceptance
proves gamma positive, so that fallback is not used. Exact evaluation and
grid transport identify the physical square with the unit square. Every
rational unit-boundary point has `abs(Q(z))>gamma`. At disk radius seven,
the computed count satisfies

```
4*LipCap(Q,7)/N <= gamma;
edgeCap(Q,7,2/N) < gamma.
```

The exact side step and inherited clearance generate every normalized
edge and line check, hence the full unit-square boundary checker at N.
The original checker is the sole boundary-check hypothesis. Coarse
refinement, exact grid transport and the unit-square factor-count theorem
give

```
index(P on the physical coarse square)
  = index(Q on the unit square at N)
  = unitSquareFactorCount(squareFactorRoots(Q,N));
0 <= index <= degree(trim(P)).
```

`lw-polynomial-square-index-factor-count` proves the equality;
`lw-polynomial-square-index-nonnegative` exports the bounds. A normal-guard
execution used `P(z)=z-(3+4i)`, anchor `2+3i`, side two and coarse
count four. The physical checker accepted, Q was exactly z, gamma was
`3/40`, factor `215` and N `860`. The generated normalized checker
accepted; the physical coarse and normalized fine perimeter indices
were both one. The fine example sampled four sides directly.

For native Euler squares, assume the existing
`lw-euler-square-index-check` accepts with step exactly `h=s/C`.
Write B for its fixed base-target, base-error polynomial and
`M=LipCap(B,gridRadius(a,s))`. The checker gives `h*M<=eta/4`
and coarse B-values outside radius eta. The sharp physical line-point
step is h, so each base-polynomial edge cap is at most eta/4.
`lw-euler-square-base-polynomial-boundary-check` therefore generates
the required physical polynomial checker; no extra polynomial certificate
is assumed.

The existing native/model index agreement and refinement laws now imply

```
0 <= nativeSquareIndex(valueError) <= degree(trim(B));
0 <= modelGridIndex(target,error,C*refinement) <= degree(trim(B));
0 <= totalResolvedCoverIndex(target,width,epsilon) <= degree(trim(B)).
```

Here `0<valueError<=eta`, `0<error<=eta`, refinement is a positive
integer, target is natural, and width and epsilon are positive rationals.
The base polynomial and its degree bound stay fixed across these later
requests. The total-cover result uses the generated cover request and
count, with no supplied cover-index hypothesis.
`lw-euler-native-square-index-positive` also proves that a nonzero native
index is positive under the same checker.

These are nonnegative finite contour and total-cover indices. Individual
retained cell indices remain signed unless further certificates are
proved for their contours. Analytic zero counts and multiplicities,
general applicability of nonzero-index certificates, and compatible
native pole-coefficient models remain open.

### Fine Euler factor candidates with a fixed count

Fix one accepted canonical native square check at anchor a, side s,
coarse count C, base target, base error and margin eta, with step s/C.
For every later natural target and rational `0<error<=eta`, let P be
the corresponding Euler square model. Its difference from the base
polynomial B is at most `(baseError+error)/4<=eta/2` at every point
in the square. Along each coarse boundary segment, the sharp step s/C
and the base coefficient budget bound B's variation by eta/4. Each
coarse B vertex is outside radius eta. Thus P is outside radius eta/4
on every rational boundary point, uniformly in its target and error.

`euler-model-square-clearance.lisp` proves the segment margin, covers
the whole side by computed coarse cells and local parameters, and
exports the result at every fine line point.

For any polynomial coefficients and positive margin g, the generic
mesh constructor is

```
F = polynomialRootCount(P,a,s,g)
  = 1 + ceil(4*s*(1+LipCap(P,gridRadius(a,s)))/g);
N = C*F.
```

It proves `2*(s/N)*LipCap(P,gridRadius(a,s))<=g` and that the
edge cap is strictly less than g. Fine physical side steps are exactly
s/N; their endpoints stay within the square's coefficient disk.
A fine value outside g therefore generates the existing polynomial
edge check. For Euler models take `g=eta/4`: all edge and line checks
are generated, yielding an accepted physical-square polynomial checker
at N. No fine boundary-check hypothesis is supplied.

Write

```
Q = polynomialSquareNormalize(P,a,s);
K = polynomialNormalizationCount(P,a,s,N);
roots = polynomialSquareFactorRoots(Q,K);
inside = unitSquareInsideRoots(roots);
M = nativeSquareIndex(baseError).
```

The existing native refinement law and physical-square factor theorem
give `unitSquareFactorCount(roots)=M`. The selector keeps every factor
whose half-open-square indicator is one. All generated factors avoid the
boundary, so selected roots lie strictly inside the unit square.
Selection preserves repeated occurrences and proves

```
len(inside) = M <= degree(trim(B)).
```

The right side uses the fixed base polynomial B, even as P's degree,
its mesh and its total number of factors change. If the native index is
nonzero, inside is nonempty. The exact constructors and results are in
`euler-model-factor-counts.lisp`.

For a positive square with `Re(a)+s<=1`, map every selected u to

```
rho = a + (s/2)*(1+i) + (s/2)*u;
entry = (rho . 1);
center = 252 + i*Im(a);
radius = 252 - Re(a) + s.
```

Strict interior membership proves `0<Re(rho)<1`, excluding zero
and one. The records therefore satisfy the existing positive-integer
pole-family predicate. Their offsets from center have positive real
part and modulus at most radius, generating the whole cluster check.
The radius is positive and the center is in the right plane. The
candidate list's length remains exactly M. For every natural start and
nonzero M, `lw-euler-model-pole-candidates-large-index` constructs an
index in `(start,start+M]`, a positive rational cap and a candidate
logarithmic-derivative coefficient outside the corresponding scaled disk.

Normal-guard execution checked the generic mesh for
`P=z-(3+4i)`, anchor `2+3i`, side two, coarse count four and
margin one half: N was 132, edge cap 1/66, the boundary checker
accepted and the perimeter index was one. A separate selection example
used roots `0,2,(1-i)/2,0`, retaining three interior occurrences.
Mapping into anchor `1/4+2i`, side `1/4`, produced

```
((3/8+17i/8,1), (7/16+33i/16,1), (3/8+17i/8,1)).
```

The family and generated cluster checks accepted at center `252+2i`
and radius 252. From start two, the search returned index five; the
computed cap was positive and the scaled candidate coefficient lay
outside it.

The fine Euler request and the factorization request are distinct.
The original constructors use the normalized square checker's clearance
for the latter. The following refinement adds an independent requested
tolerance. Native derivative/logarithmic-derivative coefficient comparisons
with uniform caps, analytic zero/multiplicity interpretation and uniform
Landau window budgets remain open.

### Independently requested factorization accuracy

The accurate constructors add a positive rational tolerance tau while
retaining the same accepted coarse boundary certificate. On a checked
unit square, write gamma for its generated clearance and set

```
epsilon = min(tau, gamma/4);
roots = normalizedFactorRoots(P,2,epsilon);
F(z) = leading(trim(P))*product(z-root_i).
```

`lw-polynomial-square-factor-request-data` proves epsilon rational,
positive, at most tau and with `3*epsilon<=gamma`. Complete
factorization therefore proves, at every rational complex z in the
radius-two disk,

```
disk(P(z)-F(z), epsilon).
```

The whole disk is covered, including its interior. A generated member
root in that disk has `disk(P(root),epsilon)`, since F vanishes there.
The existing boundary exclusion then proves all generated factors avoid
the unit-square boundary.

The factor-path collars and perturbation checks now use this independently
requested epsilon. Their computed common refinement gives

```
coarseGridIndex(P) = unitSquareFactorCount(roots)
```

for every positive tau. Tightening tau changes the factorization and
computed refinement while preserving that exact coarse index.
`polynomial-square-accurate-counts.lisp` transports the statement to
any checked physical rational square and exports the physical-root
residual bound.

For native Euler models, keep the original base certificate fixed. Let
P be a later target/error model, N its generated accepted polynomial
mesh, Q its unit-square normalization, and K its generated normalized
mesh. The accurate roots use epsilon clamped by Q's boundary clearance
at K. The new selected list satisfies, for every positive tau,

```
len(accurateInsideRoots) = fixedNativeIndex
                       <= degree(trim(basePolynomial)).
```

`euler-model-accurate-factors.lisp` also proves each selected root u is
a member of the full factor list, lies in the normalized radius-two disk,
and maps to a point rho in the physical square. The physical polynomial
residual is at most epsilon. Combining it with the native Euler model
comparison proves, for every positive evaluator request delta,

```
disk(V(rho,delta), tau + modelError/4 + delta/4).
```

The evaluator request has no additional upper-bound hypothesis here.
The model error retains the usual `0<modelError<=eta` condition.
Thus the factorization and Euler approximation requests can both be
tightened with explicit control of every selected native value.

Mapping the accurate selected roots into a strip square gives the same
unit-weight pole-family and cluster predicates as before. The family
length and bounded coefficient-search block remain the fixed native
count. `lw-euler-model-accurate-pole-candidates-small-values` certifies
the displayed native small-value bound throughout that computed family.

Normal-guard execution checked the nonconstant request clamp for P=z,
coarse count four: its checker accepted, tolerance 1/8 gave epsilon
3/160, and tolerance 1/1024 gave epsilon 1/1024. A full constant-factor
execution for P=1, coarse count one, used tolerances 1/16 and 1/128.
The generated epsilons were 1/32 and 1/128, with refined counts 132 and
516. Both returned empty factor lists, accepted the factor-away check
and disk comparison, and gave equal coarse, refined and factor indices
zero.

The following boundary comparison uses these value approximations to
control the full reciprocal sum. Interior pole coefficient comparisons,
analytic multiplicities and the uniform Landau budgets remain open.

### Logarithmic derivative on the checked square boundary

The coefficient constructor for the factor product uses repeated linear
multiplication and preserves exact evaluation. Let Q be the normalized
Euler polynomial, F the complete factor polynomial and epsilon the
clamped factorization error. At any rational center in the radius-3/2
disk, the rational Cauchy samples on its radius-1/2 circle lie in the
radius-two approximation disk. The generated boundary check for the
local difference certifies its first coefficient. This gives

```
disk(Q'(z)-F'(z), 2*epsilon)
```

throughout the radius-3/2 disk, which includes the unit-square boundary.
Trailing-zero trimming preserves derivatives and affine substitution
scales them by its slope.

The fixed physical Euler square sits inside a strict inner disk whose
gap from the model's outer disk is `Re(anchor)/4`. This gap gives a
computed cap B for the normalized derivative, independent of degree
and all later requests, when `modelError<=Re(anchor)/2`. At a normalized
boundary point z, write rho for its physical image and let A and V be
the native first coefficient and continuation value there. The first
coefficient uses radius `Re(anchor)/4`. The errors satisfy

```
dD = (side/2)*(modelError/Re(anchor) + derivativeError)
dV = (modelError + valueError)/4
disk(Q'(z) - (side/2)*A, dD)
disk(Q(z) - V, dV)
```

The native checker gives `abs(Q(z))>eta/4` everywhere on the boundary.
With `g=eta/8`, tolerance at most g, and model and value errors at most
eta/4, the corresponding denominator margins are at least g. Put

```
C = 2/g + B/g^2
E = C*epsilon + dD/g + B*dV/g^2
```

The derivative product rule proves that F'/F is exactly the reciprocal
sum over the complete finite root list, counting each occurrence. The
native quotient comparison gives

```
disk(sum_i 1/(z-root_i) - ((side/2)*A)/V, E).
```

The theorem `lw-euler-native-factor-pole-sum-error` holds at every
rational boundary point for the same square, margin and derivative
cap. The error terms can shrink independently. The following split
gives separate interior and exterior boundary terms.

### Interior poles and the bounded exterior term

The complete reciprocal sum splits exactly into the selected interior
roots and the complementary roots. Each repeated root contributes once
per occurrence. The boundary exclusion theorem makes the complementary
roots strictly exterior to the closed square.

Let Q0 be the normalized base polynomial from the fixed native check,
and let L0 be its computed Lipschitz cap on the radius-two disk. The
coarse vertex values lie outside radius eta and the variation along
each coarse side segment is at most eta/4. Thus every normalized
boundary value of Q0 lies outside radius 3*eta/4. For every selected
root u and requested tolerance at most eta/8, the factor residual
and the comparison of the two Euler models give

```
disk(Q0(u), 5*eta/8).
```

If a boundary point lay within `delta=eta/[8*(1+L0)]` of u, the
Lipschitz estimate would put its Q0-value in the radius-3*eta/4 disk.
This proves a fixed positive distance delta for the selected list.
Its reciprocal sum S is bounded by M/delta, where M is the fixed
native index and the exact length of the selected list.

Write R for the exterior reciprocal sum, B for the fixed normalized
derivative cap and `g=eta/8` for factor clearance. On the boundary,
the full quotient has modulus at most `(B+eta/4)/g`. Subtracting the
interior sum gives

```
abs(R(z)) <= (B+eta/4)/g + M/delta.
```

This bound does not depend on the number of exterior factors. The
interior sum is the same physical unit-weight pole family used by the
cluster search. With `h=side/2` and `x=forward(z)`, exact affine
transport gives `S(z)=h*sum_i 1/(x-rho_i)`. The physical exterior
term is `R(z)/h` and has the displayed cap divided by h. Under the
previous section's error assumptions, the physical boundary comparison
in a strip square is

```
disk(sum_i 1/(x-rho_i) + R(z)/h - nativeQuotient(z)/h, E/h).
```

The theorem `lw-euler-native-physical-pole-contour-model` uses the
computed pole records directly. Deriving compatible coefficients at
the Mellin centers still requires an argument relating these boundary
models to the expansion domains.

### Exterior coefficients on a centered circle

For a checked circle of radius r centered at a, the global Euler
polynomial P already supplies both the value and its formal derivative.
Let R be its outer approximation radius, with R>r. Factor P on the
radius-R disk with error epsilon to obtain F. Local Cauchy extraction
on a disk of radius R-r about each inner point now proves

```
disk(P'(z)-F'(z), epsilon/(R-r))     for abs(z)<=r.
```

The checked circle supplies a positive denominator margin. Taking
factorization error at most one quarter of the margin gives bounds
for both denominators. The complete sum of reciprocals at the circle
equals F'/F and approximates the native quotient with the factorization,
Euler model and native evaluation errors tracked separately. Each
generated root has rational coordinates, so a root on the radius r
would give a rational normalized unit-circle point where F vanishes.
The denominator bound excludes this case, producing a strict radial split.

For an exterior offset root u, put `q=r/u`. The rational cap
`(1+r^2/abs(u)^2)/2` is below one and bounds abs(q). The normalized
reciprocal at z is the geometric resolvent

```
1/(r*z-u) = (-1/u)/(1-q*z).
```

Its truncated polynomial keeps the requested coefficient exactly and
approximates the reciprocal uniformly on the unit disk. Recursive error
splitting gives a finite polynomial for the exterior sum with arbitrary
positive error and exact coefficient

```
c_j = sum_exterior (-1/u)*(r/u)^j.
```

The full circle factor sum has a computed cap C fixed by the circle
cover. For the selected interior list, let M be its length and N the
maximum squared norm, using zero for an empty list. The computed margin
`delta=(r^2-N)/(8*r)` is positive. Every interior root has distance
greater than delta from the circle. Its reciprocal sum has cap M/delta,
so the exterior sum is bounded by `C+M/delta` on every rational unit
circle node. This bound generates all the finite Cauchy checks.
`lw-euler-circle-exterior-coefficient-cap` proves the exact disk bound
with radius `C+M/delta` for every coefficient. The error in the auxiliary
polynomial can be made arbitrarily small and does not appear in the
final bound.

This route gives a cap for a fixed factor request. The shifted
polynomial argument below gives a cap across refinements.

### Stable circular factor count

For a rational unit point `w` and an interior factor root `u`, the
weighted reciprocal `r*w/(r*w-u)` equals the conjugate of the geometric
resolvent with ratio `conj(u)/r`. Its computed polynomial has constant
term one. Multiplying the exterior polynomial by `r*w` gives constant
term zero. Taking real parts removes the interior conjugations, so the
full real contour model has constant coefficient `M`.

With radius-weighted error at most `1/8` per model against the same
native logarithmic derivative, two factor sums differ in real part by
at most `1/4`. Two polynomial errors of `1/16` give a bound of `3/8`
on the difference at all computed unit samples. Finite Cauchy recovery
adds `1/8`. The integer constant difference has absolute value at most
`1/2`, which forces it to be zero.

Let `A` be the checked anchor minimum, `g` the outer gap, `K` the
factor quotient cost and `Q` the global quotient cost. For a positive
request `e`, the shared value error is `v=1/(16*(1+r))`. The model and
factorization both use `min(e,A/4,A/(1+g),v/(1+K+Q))`.
`lw-euler-circle-count-request-adequate` proves those choices meet the
comparison hypotheses. `lw-euler-circle-request-count-exact` identifies
the count for every request and target with the one computed at request
one and target zero on the same cover.

### Uniform exterior coefficient bound

Write the unit-circle sum as `S(w) = S_int(w) + S_ext(w)`. Given an
extraction error `e > 0`, approximate `r*w*S_int(w)` by the conjugate of a
polynomial `I(w)` to error `r*e/2`. Approximate `S_ext(w)` by a polynomial
`E(w)` to error `e/2`, with the desired coefficient `c_j` exact. Choose
`d` at least the degree of `I`. The expression
`w^d*conj(I(w))/r + w^(d+1)*E(w)` equals an ordinary polynomial on the
unit circle, and approximates `w^(d+1)*S(w)` to error `e`. The first
summand has degree at most `d`. The coefficient at `d+1+j` is exactly
`c_j`.

The full factor sum has a cap `C` determined by the checked circle.
The monomial has unit norm, so finite Cauchy extraction bounds `c_j` by
`C+e`. A computed positive disk-gap request would contradict any
violation of the cap `C`. Thus
`lw-euler-circle-exterior-uniform-cap` gives the same exact cap for every
order and admissible factor request on that circle. The bound uses only the full contour cap, so it remains valid as the
individual interior factors move.

### Exterior coefficient refinement

Use the same shift degree for two models on the same checked Euler
circle. It can be chosen as the larger length of the two interior
polynomials. The shifted polynomial difference has the exact exterior
coefficient difference at degree `d+1+j`. Both full factor sums agree
with the same native boundary value up to their computed quotient
errors. Finite Cauchy extraction and disk-gap exclusion give the bound
`K*(epsilonL+epsilonR)+Q*(errorL+errorR)` at every exterior order.
Here `K` and `Q` are the fixed factor and global quotient costs of
the checked circle.

`lw-euler-circle-exterior-coefficient-value` divides a desired error by
`1+K+Q` before choosing the factor request. The difference of two calls
with positive requests `eL` and `eR`, at the same order and circle, lies
in the disk of radius `eL+eR`, even if the model targets differ.
`lw-euler-circle-exterior-coefficient-cauchy` proves this using only
finite rational evaluations. The expansion-center comparison below uses the same factorization in a
smaller disk.

### Comparison at the expansion center

A checked nonzero value at the center supplies a neighborhood radius.
Let `rho` be its minimum with the circular radius `r`. The global Euler
polynomial has a positive lower bound on the closed disk of radius
`rho` when its value error is within the local anchor error. The factor
polynomial stays nonzero when its error is at most the computed margin.
Thus all the original outer model's roots are strictly outside this
inner disk.

The full reciprocal sum is uniformly close to the native Euler
logarithmic derivative on that disk. An exterior resolvent polynomial for
the full root list keeps the exact coefficient in the variable `w` with
physical offset `rho*w`. Generated finite Cauchy checks compare it to
the native Euler log polynomial at that same scale.

`lw-euler-circle-center-split-coefficient-comparison` reflects the
expansion and removes the radius scaling. It bounds the difference
between the raw Taylor coefficient in the variable `center-s` and the
sum of the selected-pole and exterior coefficients. The coefficient
error is the computed disk error divided by `rho^j`. The separate
`lw-euler-circle-reflected-exterior-coefficient-cap` gives cap
`C/r^j` on the exterior coefficient.

### Transport through the Mellin normalization

Let `W` denote the native Euler logarithmic derivative of the regularized
zeta value, and let `F` denote the normalized Mellin function. The exact
arithmetic identity is

```
s(s-1) F(s) = (s-1) + gamma*s - W(s).
```

The affine part has zero coefficients from order two onward. In the
reflected variable `z = center-s`, multiplication by `s(s-1)` turns
the coefficient at order `j` into

```
center*(center-1)*A_j + (1-2*center)*A_(j-1) + A_(j-2).
```

ACL2 proves the coefficient identity for polynomials and generates finite
Cauchy checks for the normalized approximation error. The native Mellin
coefficient evaluator agrees with the polynomial coefficients to
computed errors. `lw-euler-circle-mellin-split-comparison` bounds the sum
of the three-term expression and the reflected full factor coefficients.
`lw-euler-circle-mellin-pole-comparison` removes the exterior term at cost
`C/r^j`. These theorems use the checked outer circle, a checked nonzero
center with real part above three, and admissible model errors.
Generation of the models from general zero data and coupling to the
window budgets remain required.

### Finite pole clusters and bounded coefficient search

The ten books from `weighted-power-sums` through `zeta-cluster-search`
prove a finite cluster argument without pole separation. They use exact
rational complex pairs, so the finite pole records here are not yet a
representation theorem for arbitrary analytic zeta zeros.

For `S_k=sum_i w_i*z_i^k`, `M=len(entries)>0`, `abs(z_i)<=1`, and
`abs(S_k)<=A` for `0<=k<M`, ACL2 proves the entire prefix through N is
bounded by

```
A * [3*(N+1)]^(M-1).
```

The first difference `S_(k+1)-z_1*S_k` has M-1 nodes and weights
`(z_i-z_1)*w_i`. This eliminates a node without division. Prefix
propagation and induction on M prove the displayed bound. Repeated nodes
and zero weights are allowed.

For outer nodes `abs(z_i)>=1`, reverse at `n=K+M`: the new nodes are
`1/z_i` and weights `w_i*z_i^n`. The first M reversed samples are the
original orders K+M down to K+1. Consequently,

```
all abs(S_k)<=A for K<k<=K+M
  => abs(S_0)<=A*D,
D = [3*(K+M+1)]^(M-1).
```

If S_0 is nonzero, `L1(S_0)/(8*D)` is positive. A bounded search in
those M orders returns a sample outside that disk.

For a nonempty finite pole family `(rho_i . m_i)`, the cluster check
requires positive integer multiplicities, `rho_i!=0,1`,
`Re(a-rho_i)>0` and `abs(a-rho_i)<=r`, where r is positive.
Set `z_i=r/(a-rho_i)` and `w_i=m_i/(a-rho_i)`. The check derives
outer-node bounds and positive real part of the total weight, which is
also the finite factor model's logarithmic derivative at a. Thus no
nonzero-total-weight hypothesis is supplied to the cluster search.
It returns `K<k<=K+M` such that

```
abs(r^k * W_k) > T,
W_j = sum_i m_i/(a-rho_i)^(j+1),
T = L1(W_0)/(8*D).
```

The existing normalized principal parts use
`R_i=-m_i/(rho_i*(rho_i-1))`. Write
`A_j=sum_i R_i/(a-rho_i)^(j+1)`,
`q0=a*(a-1)`, and `q1=1-2*a`. For j>=2 the exact identity is

```
q0*A_j + q1*A_(j-1) + A_(j-2) = -W_j.
```

For the scaled coefficients `B_j=r^j*A_j`, the left side becomes
`q0*B_j+r*q1*B_(j-1)+r^2*B_(j-2)`. Its norm budget is

```
Q = 1 + L1(q0) + abs(r)*L1(q1) + r^2 >= 1,
tau = T/(2*Q) > 0.
```

For K>=1, `lw-zeta-cluster-large-index-certificate` computes an index
in `[K-1,K+M]` with `abs(B_index)>tau`. All M+2 samples cannot
satisfy the tau bound, since that would put the selected logarithmic derivative sample in the T/2 disk. Initial normalized aggregate
cancellation is allowed. An approximation within tau/4 stays outside
the tau/2 disk; both the search and this error margin are certified.

These are finite rational coefficient results. The preceding candidate
construction now supplies computed unit-weight families from checked
native squares. Compatible comparisons with native pole/factor
coefficients, analytic multiplicity interpretation and uniform budgets
placing these blocks inside the Landau window's admissible orders remain
required.

### Actual Mellin moments and Euler coefficients

The seven books from `euler-normalized-physical-comparison.lisp` through
`euler-window-coefficients.lisp` connect every computed Mellin moment to
the actual normalized Euler coefficient family.

Let `a=rate+i*height` satisfy `rate>3`. At an accepted local coarse
check, write `r=rLocal>0` for its normalized physical radius and `K`
for its fixed polynomial cap. For every natural `j`, the canonical
physical coefficient `B_j(eA)` and any constructed local polynomial
`P_target,EP` satisfy

```
disk(B_j(eA)-coefficient(P_target,EP,j), eA/2+EP/(2*r^j)).
```

The computed radius `d=min(r,(rate-3)/2)` is positive. Reflection gives
the polynomial `Q(z)=P(-z)`; its j-th coefficient is
`(-1)^j*coefficient(P,j)`, and its cap on `disk(z,d)` is `K`.
Every point of that disk has `Re(a-z)>3` with a generated native
nonzero check. For the actual improper polynomial `M_target,EM` on
the same disk, constructed uniform comparisons give

```
disk(Q_leftTarget,EP(z)-M_rightTarget,EM(z), EP/2+69*EM/64).
```

A zero-padded difference polynomial, rescaled by `d`, has every
finite Cauchy boundary check generated at this cap. Coefficient
extraction therefore proves, for every `j` including indices outside
either original coefficient list,

```
disk(coefficient(Q,j)-coefficient(M,j), (EP/2+69*EM/64)/d^j).
```

Define `A_j(eA)=(-1)^j*B_j(eA)`, the coefficient name for `F(a-z)`.
Combining these bounds with actual Mellin moment recovery and eliminating
the arbitrary auxiliary precision proves
`lw-mellin-euler-moment-comparison`:

```
disk(I_j(a,eI)-A_j(eA), 5*eI+eA/2).
```

The elimination uses the positive rational cost `1+1/r^j+2/d^j`
and the computed disk-gap refinement. It introduces no convergence or
coefficient-agreement hypothesis. Requests `eI=E/10` and `eA=E`
meet any requested positive output error `E`.

`euler-mellin-native-coefficients.lisp` chooses outer radius `rate/2`
and the generated native coarse request. Thus
`lw-complex-mellin-euler-coefficient-value(rate,height,j,eA)`
needs no caller-supplied clearance check when `rate>3`.
It has half-sum Cauchy radius, fixed cap `K/r^j`, the same all-index
moment comparison, and half-sum agreement with every independently
accepted local coefficient model.

Finally set `j=windowIndex(Y)`, `W=8*C+10` and `b=252-p/q`.
For rational `Y>1` above the kernel window threshold, rational
`height`, `C>=0`, encoded `0<=p/q<=1` and positive requests
`eH,e0`, failed search proves

```
disk(A_j(252+i*height,eH), W/b^(j+1)-Re(A_j(252,e0))+(eH+e0)/2).
```

`lw-eventual-failed-search-euler-coefficient-bound` proves this bound
and its radius is nonnegative. The same-error corollary replaces the
half-sum by `e`. A temporary Mellin request costs `11*margin`;
disk-gap refinement removes it entirely. The height-zero coefficient
remains part of the bound.

These results identify actual right-plane coefficients and transfer the
search inequality to them. General zero-region factor construction,
complete zero covers and multiplicity handling, and the analytic
interpretation of the arithmetic theorem remain required.

### Constructed finite logarithmic-derivative models

`complex-quotients.lisp` derives division error bounds from value errors.
For actual numerator/denominator `N,D`, approximations `n,d`,
denominator clearances `A,B>0`, and `disk(n,M)`, it proves

```
disk(N/D-n/d, numeratorError/A + M*denominatorError/(A*B)).
```

The clearances are checked squared-norm inequalities on `D` and `d`.
The computed common input precision

```
eta = e / (2*(1 + 1/A + M/(A*B)))
```

makes both value errors at most `eta` sufficient for output error `e`.
The quotient product rule and the error from an approximate factorization
`value ~ P*h`, `derivative ~ P'*h+P*h'` are also proved.

`polynomial-factor-model.lisp` constructs

```
P(s) = product_rho (s-rho)^nu,
L(s) = sum_rho nu/(s-rho),
```

together with the formal derivative, and derives `P'/P=L` away from the
recorded factors. A positive family clearance discharges that exclusion
check. Multiplicities are retained throughout.

`zeta-factor-transform.lisp` normalizes each contribution at `s=1`.
Away from the displayed denominators, the exact identity is

```
-nu*(1/(s-rho)-s/(1-rho))/(s*(s-1))
  = (-nu/(rho*(rho-1)))/(s-rho) - nu/(rho*s).
```

The constructed rational extension cancels the apparent pole at 1; its
principal-part split holds there too. For a finite family, the normalized
transform of the actual product and formal derivative is its recorded
zeta-shaped principal-part sum plus `c0/s`, where

```
c0 = -sum_rho nu/rho.
```

For `|s|>=a>0`, that explicit regular correction has cap `L1(c0)/a`.
Its j-th coefficient at a center with the same clearance has cap
`L1(c0)/a^(j+1)`. These are proved bounds on a constructed correction;
no analytic-remainder representation is assumed for them.

`polynomial-divided-difference.lisp` constructs the polynomial
`D_aP` by synthetic division and proves

```
P(s)-P(a) = (s-a)*D_aP(s).
```

It is defined at `s=a` without a zero denominator and has one fewer
coefficient than a nonempty input. This supplies finite polynomial
normalization at 1 for a regular logarithmic-derivative model.

These results construct the finite algebraic pieces. The actual zeta
factorization, approximation of its remaining nonvanishing factor,
continuation to the zero region and compatible uniform remainder bounds
still need proof.

### Constructed regular certificates

`polynomial-maps.lisp` supplies coefficient multiplication and constant
addition; `polynomial-affine.lisp` computes `P(z+slope*w)` by Horner
composition and proves its exact evaluation and coefficient count.
`polynomial-addition.lisp` combines coefficient lists and derives a
unit-disk cap and accepted boundary checks from their finite coefficient mass.

`polynomial-normalization.lisp` takes a polynomial logarithmic derivative
`L` and correction `k`. It constructs the numerator polynomial

```
N(s) = L(1)+k-D_1L(s)
```

and proves, away from the original denominators,

```
-[L(s)-s*L(1)+k*(1-s)]/[s*(s-1)] = N(s)/s = B(s)+a0/s.
```

Here `a0` is the first coefficient of `N`, and `B` is its coefficient
tail. The constructed value is defined at 1 without a zero denominator.
Both the normalization identity and the polynomial-plus-origin-pole split
are proved.

`pole-polynomials.lisp` constructs coefficients for `c/(z-R*w)` by
multiplying a geometric coefficient list by `c/z`. A checked clearance
`a<=|z|` with `0<=R<a` supplies the ratio cap `q=R/a<1`.
The existing pole precision constructor and geometric truncation count
give any requested error `e>0`, uniformly on `disk(w,1)`.
Every adequate truncation has cap

```
L1(c/z)/(1-q)+e.
```

Thus its cap need not grow with its degree. The book also proves that
the actual finite boundary checker accepts that cap.

`zeta-regular-model.lisp` combines the factor correction with this
normalized polynomial part. Let

```
c = -sum_rho nu/rho + a0,
F(w) = B(z-R*w),
n = max(target+1, computedPolePolynomialCount(c,z,R,a,e)),
U(w) = F(w) + polePolynomial(c,z,R,n).
```

The coefficients of `F` and `U` are constructed, rather than supplied.
For `0<e<=1`, the cap

```
M = coefficientMass(F) + L1(c/z)/(1-R/a) + 1
```

bounds `U` on the unit disk and makes every finite boundary check pass.
It depends on the fixed finite input model and contour; it contains
neither `target` nor `e`. The generated record is

```
[coefficients(U), len(coefficients(U)), R, M, 1].
```

`lw-zeta-regular-model-certificate` proves that the existing
`lw-mellin-regular-certificatep` accepts this record at `target`, for
`R>0`. The degree field is a conservative upper bound. The extraction
error is fixed at 1; its scaled contribution is absorbed using
`d/R<1` in the dominance theorem.

With logarithmic-derivative input `sum_rho nu/(s-rho)+L(s)`, the
normalized transform is proved equal to
the recorded principal parts plus the constructed regular function.
On `disk(w,1)`, away from its poles and the origin, replacing that
regular function by `U(w)` has error at most `e`.

These statements generate regular certificates for a fixed finite model.
The all-index moment identity above identifies the actual Euler and
Mellin coefficients in the right plane. These finite certificates still
require actual zeta factor models and accepted comparisons with that
coefficient family. Uniform bounds must still be
proved when the finite logarithmic-derivative model itself changes with
the requested analytic precision.

### Checked Mellin pole models

`polynomial-difference.lisp` constructs `P-Q` exactly: its coefficients
are the pointwise differences and its evaluation is the difference of
the two evaluations. A finite Cauchy check on this difference polynomial,
with cap `delta` and extraction precision `e/2`, bounds its selected
coefficient by `delta+e/2`.

`mellin-pole-bridge.lisp` constructs `Q` from the selected principal part,
a finite family of other principal parts and rescaled regular coefficients.
It has the same length as the actual improper polynomial `P`.
Together with the moment recovery for `P`, the named finite checker
`lw-mellin-model-boundary-check` proves

```
disk(I_H(e/64)-modelCoefficient_H(j), delta_H+e).
```

Thus coefficient agreement is derived from a boundary comparison.
Accepted model checks and the general-radius dominance hypotheses give

```
1/2 <= Z*(momentCap+delta_H+e)*d^(j+1),  Z=M1*M2.
```

### Real anchor and conditional window witness

`mellin-real-anchor.lisp` uses a separate model at center `(252,0)`.
It sets the selected multiplicity to zero; all recorded poles are in its
finite family. This asserts no zero at the placeholder location.
If that family's residue mass is `M0`, its clearance is `A`, its regular
contour radius is `R0`, its regular Cauchy cap plus extraction error is
`K0`, and its comparison cap is `delta_0`, then

```
-Re(I_0(e/64)) <= M0/A^(j+1) + K0/R0^j + delta_0 + e.
```

`mellin-window-certificate.lisp` composes this with failed search at
precision `e/64`. Write `b=252-p/q` and `W=8*C+10`. Failure would force

```
1/2 <= Z*d^(j+1) *
  (W/b^(j+1) + M0/A^(j+1) + K0/R0^j + delta_H + delta_0 + (129/64)*e).
```

All quantities are rational. An accepted strict upper budget below
`1/2` contradicts failure and forces the actual search to succeed.

`mellin-window-budget.lisp` computes sufficient budgets. Its
`lw-mellin-window-decay-index` is the maximum of three family indices,
with masses `8*Z*W`, `8*Z*M0`, and `8*R0*Z*K0`, and respective
clearances `b`, `A`, and `R0`. For `d` below all three clearances and
`j` above this maximum, each geometric term consumes at most `1/16`.
With `S=Z*d^(j+1)`, choose

```
0 < e <= 1/(128*(1+S)),  0 <= delta_H <= e,  0 <= delta_0 <= e.
```

The comparison errors consume at most another `1/16`, so the budget is
strictly below `1/2`. The checker also retains the selected model's own
computed dominance index and the kernel window threshold.

The theorem `lw-mellin-computed-budget-window-witness` then returns the
actual search result and address: the address is rational, lies in the
window, and has a strictly positive lower signal enclosure at precision
`1/4`. Both model boundary checks and all separation bounds remain
hypotheses. Proving their generation from general analytic zeta data,
with compatible uniform constants and complete zero covers, is still
required for the full Landau reduction.

### Checked circular clusters

A checked circle fixes the interior count `M` across fine models. Its
base polynomial and boundary clearance give a positive collar width
`delta`, so all selected offsets lie within `d=r-delta`. The joint
request also keeps those offsets away from the expansion center. For
`M>0`, the unit-weight reciprocal power sums select an order `j` among
`j0+2,...,j0+M+1`, where `j0=windowIndex(Y)`. The selected interior
coefficient lies outside the disk of radius

```
M / (8 * (3*(1+j0+2+M))^(M-1) * d^(j+1)).
```

Above the computed threshold for block width `M+1`, failed search
bounds the Mellin coefficients at `j-2,j-1,j` on the same window.
Clearing the quadratic denominator relates their weighted sum to the
selected interior coefficient. The comparison contributes its explicit
model error and an exterior bound `E/r^j` with fixed `E`. The sum of
these caps and the failed-search cap cannot be at most the displayed
radius. The theorem `lw-euler-circle-window-cluster-witness` therefore
forces search success from that scalar inequality.

The exponential-decay lemma computes a threshold for
`mass*(offset+j)^degree*ratio^j` given `0<=ratio<1`. With clearance `R>d`, it gives a threshold for `E/R^j` to
use any positive fraction of the selected-pole bound, uniformly for
`j>=j0`. This applies to the exterior term with `R=r`.

For a common request `0<e<=1`, the explicit model comparison error
is exactly `e` times its value at request one. The maximum absolute
gain over the finite block gives a single request that attains any
positive tolerance throughout the block. The weighted window mass, the
exterior coefficient and a supplied height-zero bound each use one
eighth of the selected-pole bound above a computed order. The common
precision allocates another eighth each to model error and rounding.
The checked height-zero data bound the negative real part of the
native coefficient at orders `j-2,j-1,j` by `M_real/R_real^k + e`,
where `R_real>d`.

The theorem `lw-euler-circle-computed-window-certificate` computes the
window threshold from these constants. For each later window, its
computed search returns a rational address and a positive lower signal
enclosure. A checked circle with positive count, the strict clearance
inequalities and the height-zero estimate are hypotheses. The
polynomial real-anchor model replaces gamma by its own value at one,
so the removable factor cancels exactly. At one, the factor model agrees with the computed Euler constant to an
explicit error. A checked circle with no interior factors gives a uniformly
capped exterior polynomial. The remaining inverse is polynomially
approximated up to any strict radius inside its pole. On a circle of
radius `rho` between the distance to one and the checked empty radius,
the product polynomial has a fixed boundary cap `M`. Finite sampling
bounds each of its coefficients by `M/rho^j`. A comparison on a smaller
center disk has linear error in the common request. Finite Cauchy
extraction and independent chart transport compute sufficient precision
for the canonical height-zero bound `M/rho^j+e`. The theorem
`lw-euler-circle-pair-window-certificate` inserts the result for all three
required orders. The remaining hypotheses are the two checked covers,
their counts and the radius inequalities.

### Selecting radii and bounding finite factor counts

`lw-circle-finite-separated-radius` returns a rational radius in any
specified positive-width interval. If the final subinterval has width
`w`, every supplied root's squared radius differs from the selected
squared radius by at least `g = w^2`. On the circle of radius `r`,
`lw-circle-radial-clearance-valid` gives the Euclidean distance lower
bound `g/(1+g+4r)`. The product lower bound includes the leading
coefficient and counts repeated roots. The Euler anchor check follows
when the polynomial and factorization errors meet explicit fractions of
that lower bound.

For a finite list of off-axis strip points, `lw-circle-pair-radius-selection`
chooses a modulation height and three ordered radii. The first admits a
smaller modulated contour with the selected point inside. The second
exceeds 251 and may serve as the normalization radius. The third lies
strictly below the input limit and excludes every supplied point from
the closed real-centered disk.

`lw-circle-inner-factor-count-bound` works in unit-disk coordinates.
Reflect each factor with squared root radius at most `u < 1`, replacing
`z-a` by `1-conj(a)*z`. If `m` factors are reflected, the ordinary
squared center value is at most `u^m` times the reflected squared center
value. The boundary norms coincide, so finite Cauchy extraction with
margin 1 bounds the reflected center by `(M+1)^2` in squared norm.
The proved upper count bound depends on `u`, the accepted boundary cap
`M` and the positive lower bound for the ordinary squared center value.
The finite boundary sample count can depend on degree.

`lw-euler-circle-inner-factor-count` applies this bound to the generated
Euler factors on every disk strictly within the positive half-plane,
using coordinates scaled to the unit disk. If the accepted center
clearance size is `S`, each approximation error is at most
`min(1,S/64)`. The original squared center value is at least
`(S/8)^2`, and the fixed boundary cap is one plus the native uniform
coefficient cap. These inputs to the count limit are independent of the
requested polynomial degree and both approximation errors.

`lw-euler-circle-bounded-radius-valid` generates the center check for
`rate > 3`. For a normalized radius interval `(l,h)` with
`0 <= l < h` and `h^2 < u < 1`, only roots of squared radius at
most `u` shrink the interval. With count budget `N`, the returned gap
works for all roots and equals
`min(((h-l)/4^N)^2, u-h^2)`. This number stays fixed across both
approximation requests. Each request pair may choose a different
radius in `(l,h)`.

### Comparing the reflected and original products

For a radius gap `g` shared across Euler approximants, set
`delta = g/(5+g)`. A reflected factor has norm at most 2 on the unit
disk. The corresponding original factor has norm at least `delta`
on the separated circle. With inner count at most `N`, a positive
reflected squared lower bound `B` therefore gives original squared
lower bound `B*(delta^2/4)^N`. The contribution from unreflected
factors is the same in both products.

`lw-circle-reflected-factor-normalization-valid` writes each reflected
model factor as `c*(1-a*z)` with nonzero `c`. For the inner disk of
radius `r` and cutoff `r^2 < u < 1`, every `a*z` lies in the disk of
radius `(1+r^2/u)/2 < 1`. Signed rational logarithm enclosures compose
through multiplication with the sum of the three requested errors.
If `z` lies in a disk of radius `d <= 1/4`, the lower enclosure for
`log(|1-z|^2)` differs from `-2 Re(z)` by at most `e+19*d^2`.
For a sample `z` in a disk of radius `q < 1`, one step of width
`h` on the segment has relative increment
`u = h*z/(1-t*z)`, of norm at most `d = h*q/(1-q)`.
`lw-complex-log-path-sum-bound` accumulates the signed logarithm error
`4e+19*d^2` per cell when `d <= 1/4`.
`lw-rational-monomial-grid-error` bounds the left rectangle sum for
`t^k` between `1/(k+1)-h` and `1/(k+1)` on the unit interval.
The truncated geometric rows integrate coefficient by coefficient.
For a target tolerance `T > 0`, let `A=q/(1-q)`. The certified
construction chooses an order `N` with `q^N <= T/(8*(1+A))` and
a mesh count `M` at least `4*A + 4*(19*A^2+2*N)/T`.
For each rational `z` with norm at most `q`, the scalar logarithm
lower endpoint at any request `0 < e <= T/(16*M)` differs from
`-2*Re(sum_{j=1}^N z^j/j)` by at most `T`.
The reflected log comparison sums the factor errors. With
`m` factors, the budget is `m*(T+9e)`, since each log-ratio increment
uses three signed products. The Harnack polynomial uses
`T=1/(32*(1+m))` and a compatible scalar request, so the comparison
error is at most 1.

### Reflected product floor from a checked cap

Let `c>0` bound the reflected squared center value below and let
`M` bound its squared boundary samples on a strict disk. Shift the
doubled logarithm polynomial by `K=2+M+1/c`. Its real part is
nonnegative at those samples. One finite Cauchy check gives the
interior upper bound `K+r*(2*K+4)/(1-r)` on the real part inside
normalized radius `r<1`. Dyadic growth of the signed logarithm
then gives an explicit positive squared norm floor for the reflected
product. This floor depends on `c`, `M` and `r`. Finite Cauchy coefficient caps now derive this check from the original
unit-boundary cap `C`. At fixed outer normalized radius `s<1`, the
reflected squared boundary cap is `((C+1)/(1-s))^2`, and reflection
transfers the original squared center lower bound to the reflected
model.

Combining this floor with the fixed radius margin gives a positive
squared value floor `B` for the original factor polynomial. The
uniform distance `L=B/(1+B)` is computed before choosing any fine
requests. Under the input radius inequalities,
`lw-euler-circle-uniform-anchor` applies to every rational point on the
generated circle, using both approximation errors at most
`min(1,S/64,L/16)` and anchor error at most `L/32`. It proves the
native value check and gives a clearance size of at least `L/2`.
The thresholds are independent of both model requests.

For a contour of physical radius `r` inside the global Euler disk
of radius `R`, choose the common local outer radius `a=(R-r)/2`.
If `M` is the global Euler coefficient cap, the native value cap
is `M+2`. Each translated local polynomial on the unit disk has
value cap `M+4` and Cauchy coefficient cap `M+5`. A geometric
sum on the half disk bounds its physical slope by `K=4*(M+5)/a`.

With center real part `sigma` and squared radial gap `g` from the
pole, the common patch radius is at least

```
min(a/2, 1, (L/2)/(64*(1+K)), (sigma-R)/4, (g/(1+g+4*r))/4).
```

The positive mesh count for reach `d` is
`1+lw-precision-fuel(2*r,d)`. The chart reach `2*r/count`
is at most `d`. A rational subinterval of the original normalized
band reserves the pole gap before the Euler precision requests
are set. The constructor `lw-euler-circle-generated-cover`
returns a physical radius strictly between `R*lower` and
`R*upper` and both checked charts. Its validity theorem also
proves the Euler center check. The result requires `3<sigma`, `0<R<sigma`
and `0<=lower<upper<scale` with `scale^2<cutoff-square<1`.
If the selected model has no inner factors, reflection leaves its
polynomial unchanged and the finite Harnack floor applies throughout
each strict inner disk. For normalized evaluation at `scale*point`,
with `|point|<=inner<1`, let `D` be the distance floor computed
from the squared center bound, the common cap and these two radii.
Put the canonical polynomial and factor errors at most `D/8`, and
request the Euler value at error at most `D/8`. A value in the
disk of radius `D/2` forces an inner factor. If the normalized
cutoff is physically strictly inside a checked contour,
`lw-euler-circle-positive-count-from-small-value` forces its actual
interior count to be positive. The proof normalizes the physical
factor list itself, preserving the choices used by the exact count.
Conversely, a positive checked count produces an interior rational
offset on a fine canonical request. The first retained factor vanishes
there and the Euler value lies in the requested tolerance disk.
`lw-euler-circle-empty-count-from-reference-model` excludes this probe
using a larger reference model with no inner factors and a shared
Harnack floor. The reference model's two errors must fit the same
`D/8` bound, and its strict inner disk must contain the checked circle
and its interior. The paired small-value and empty-reference evidence
still needs to be obtained from the encoded zero hypotheses.

## Native clearance near the real axis

For positive rational `s`, pairing the finite alternating Dirichlet
sum gives a first-pair gap bounded below by
`g(s)=1-1/(1+s/2)`. ACL2 chooses the common precision to retain
at least half that gap. Subtracting twice the sample at two times
the shorter Euler prefix from the next dyadic prefix cancels the
endpoint term to a computed error. This compares the scaled
alternating sum with the Euler continuation using the same
finite arithmetic evaluators.

For `s!=1` and native request at most `abs(s-1)*g(s)/64`, the
native Euler value has squared norm greater than
`(abs(s-1)*g(s)/32)^2`. The checked neighborhood at one gives
a positive bound through that point. Given `a>0`, the functions
`lw-euler-real-axis-floor` and `lw-euler-real-axis-request`
give a uniform distance floor and precision for all `s>=a`.
Inside a fixed real-centered Euler disk, the common local slope
gives a computable vertical width `lw-euler-near-real-radius`
with Euler distance floor at least one eighth of the real-axis
floor. These estimates apply to native Euler samples.

## Native clearance to the right of one

For a rational sampling rate `a > 1`, set
`D(a)=64/(a-1)^2`, `C(a)=13+D(a)`, and
`F(a)=(a-1)/(32*C(a))`. The dyadic tail from `2^b`
has mass at most `D(a)/(b-1)` plus the computed primitive
rounding term. The full dyadic prefix has mass at most `C(a)`
at the chosen request.

Finite Möbius weights satisfy `sum_{d|n} mu(d)=0` for
`1<n<=N` and give one at `n=1`. In the product of the
two length-`N` Dirichlet prefixes, the omitted pairs with
`mn>N` have at least one index beyond the computed square
cutoff. Their mass is at most twice the prefix mass times the
tail mass. Both this term and pair-rounding error fit inside
radius `1/2` of the inverse identity. The resulting ordinary
prefix lies outside the disk of radius `1/(4*C(a))`.

The dyadic Euler prefix multiplies that ordinary prefix by
`(a-1)+i*h` and adds the terminal sample. A common primitive
request bounds the terminal sample and continuation error.
For any rational `s>=a`, rational height `h` and native
value request `0<e<=F(a)`, the sample at `s+i*h` is outside
the closed disk of radius `F(a)`. This is
`lw-complex-euler-right-uniform-clearance`. Together with the
near-real bound, it gives the strict probe gap for the paired
contour construction. [Final reduction](acl2-interpretation.md)

## Computed rational grid

The paper's Proposition 6.5 uses an ideal grid with spacing
`m*Y^theta/(4*L_h)` and endpoint `Y^(3/2)`. For rational input these are
generally real, not rational. Its real grid argument can motivate the
algorithm, but cannot itself supply the promised rational addresses or a
rational precision budget. `acl2/rational-window.lisp` now proves a
conservative replacement, including its computed precision budget.

A conservative implementation can choose rational `d > 0` below the allowed
spacing and a certified lower endpoint `B <= Y^(3/2)` with
`Y^(3/2) - B <= d`. Set `N = ceil((B-Y)/d)` and
`a_k = min(Y + k*d, B)`. Every address is rational and lies in the original
window; every point in that window is within `d` of an address, including
the omitted tail above `B`. Certified rational bounds must also replace
the ideal formulas for `m`, `L_h`, and the primitive precision.

The implementation uses bounded bisection and a mesh with a shortened final
gap. ACL2 proves endpoint bracketing, coverage and window-specific search
success. Lean's `roundedMesh_covers_real_window` proves the rational
inequalities cover every real point of the original window, including its
tail. The ACL2 reduction uses this mesh with the actual signal's
precision and effective transport.
[Encoded-zero theorem](../acl2/euler-window-encoded-zero.lisp)
