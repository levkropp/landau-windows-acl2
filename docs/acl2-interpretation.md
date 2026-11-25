# The ACL2 windowed ceiling theorem

The certified theorem `lw-euler-window-encoded-zero-reduction` takes a
rational region, a small rational Euler sample in that region, and a
window start. It supplies a computed threshold and certifies a rational
address with a strictly positive lower bound for
`Gz(x) − C*x^(p/q)`. Both the threshold and the sample request depend
on the region and ceiling data, so the point can be chosen afterward.
[ACL2 theorem](../acl2/euler-window-encoded-zero.lisp)

## Arithmetic statement

Let `theta = p/q` with `0 <= p < q`, and take rational data
`251 < cap < 252 − theta`, `0 < slack < cap`, center height `h`, and
`C >= 0`. The region is the closed disk of radius `cap − slack`
around `252 + i*h`. An **encoded zero** in this disk means that for
every rational `e > 0` there is a rational coordinate pair `u` such that
`lw-euler-window-approximate-zerop cap slack h u e` holds. This checks
that `u` is inside the disk in offset coordinates and that the native
Euler value at that point and request `e` has norm at most `e`.

Set `r = lw-euler-window-zero-sample-request(cap, slack, h)` and take
`Y0 = lw-euler-window-ceiling-threshold(cap, slack, h, C, p, q)`.
ACL2 proves `r > 0` and that `Y0` is a positive integer. An encoded zero
supplies a witness at `e = r/4`. For every rational `Y >= Y0`, the
certified theorem derives a successful `lw-landau-window-search` with
`Y <= x`, `x^2 <= Y^3`, and positive lower endpoint. Equivalently, a
failed search excludes the encoded zero by excluding every witness at
the one computed precision. Universal quantification over precisions
and existential quantification over rational pairs are ordinary
arithmetic quantifiers over codes.
[Threshold and certificate](../acl2/euler-window-ceiling-reduction.lisp)

The real-circle scan begins with certified zero count. It either reaches
an empty circle near `cap` or stops at a positive count immediately
outside an empty circle. In the first case the supplied probe gives the
positive modulated count. In the second case an arbitrarily fine
interior probe of the positive real-centered count gives the modulated
count. The real-axis and right-half-plane clearance bounds give a
uniform gap between the probe's horizontal displacement and the
real-centered radius. This permits an empty real circle with an
interior normalization radius strictly outside the modulated circle.
The argument uses small values and finite counts throughout, so it
handles multiple and clustered zeros through the same interface.
[Paired contour construction](../acl2/euler-window-circle-pair.lisp)

## Identifying the zero predicate

Write `Z(s) = riemannZeta₁(s)`, the entire function that equals
`(s − 1)ζ(s)` away from one and has `Z(1) = 1`. For rational
`s = a + i*t` with `a > 0`, let `V(s,e)` denote the complex
interpretation of `lw-complex-euler-continuation-value a t e`.
The following mathematical argument interprets the certified
arithmetic estimator:

```text
|V(s,e) − Z(s)| <= e/4.
```

For fixed integer `n >= 1`, the ordinary Dirichlet sample at
primitive request `eta` tends to `n^(−s)` as `eta` tends to zero.
The rectangle sums for the decreasing function `1/x` enclose the
logarithm, with width at most the request. At the resulting rational
complex argument, the finite exponential sum differs from its
convergent Taylor series by at most `eta`. This follows by taking
the limit in `lw-complex-exp-value-tail`, whose disk bound holds for
every sufficiently long finite sum.
[Logarithm bounds](../acl2/log-bounds.lisp) ·
[Exponential tail](../acl2/complex-exp.lisp) ·
[Dirichlet sample](../acl2/mangoldt-dirichlet-convolution.lisp)

Fix a dyadic cutoff `N + 1 = 2^b` with `b >= 2` and
`2^b >= a + |t|`. The certified fixed-truncation estimate bounds
the discrepancy of `V(s,e)` from the finite dyadic model by
`e/4 + A(s)/(b−1) + B(s,b)*eta`. Let `eta` tend to zero
with `b` fixed. The model tends to

```text
U_N(s) = (s−1) * sum_{n=1}^N n^(−s) + (N+1)^(1−s).
```

Put `X = N+1`. Integrating on each unit interval and telescoping gives
`sum_{n=1}^N n^(−s) = N*X^(−s) + s*integral_1^X floor(x)*x^(−s−1) dx`.
Splitting `floor(x) = x − fract(x)` and substituting yields

```text
U_N(s) = s − (s−1)*X^(−s)
           − s*(s−1)*integral_1^X fract(x)*x^(−s−1) dx.
```

The equality also holds at one. For `a > 0`, the integral tail has
norm at most `X^(−a)/a`. Thus `U_N(s)` tends to `Z(s)`
by the fractional-part identity proved in Lean. Letting `b` tend to
infinity removes the remaining `A(s)/(b−1)` term and proves the
claimed `e/4` estimate.
[Fixed truncation](../acl2/euler-fixed-truncation.lisp) ·
[Fractional-part identity](../lean/LandauWindows/Soft/ZetaReal.lean)

A zero of `Z` in the interior of the disk gives an encoded zero.
For every `e > 0`, continuity and rational density give a point in
the disk with `|Z(s)| < 3e/4`. Its native value is inside the required
disk of radius `e`. Conversely, select a sequence of probes with
errors tending to zero. Their points lie in one compact disk contained
in the right half-plane. At a subsequential limit the norm of `Z`
is zero, since it is at most `5e/4` at each corresponding probe.
Since `Z(1) = 1`, this is a zero of `ζ`.

## Interpreting the window witness

The prime-power classifier is exact. The log rectangles enclose
`log x`, the Euler bounds enclose `gamma`, and the rational power
bracket encloses the positive `q`th root of `x^p`.
For `x >= 1` the ramp `max(0,x/n−1)` vanishes above `x`, and
`lw-signal-count` covers every integer up to `x`. Finite interval
addition, scaling and subtraction in `lw-signal-bounds` therefore
enclose

```text
sum_{n<=x} Lambda(n)*(x/n−1) − x*log(x) + (1+gamma)*x − C*x^(p/q).
```

The returned lower endpoint `L > 0` proves the strict violation. For
a margin of the form `m*x^(p/q)` one can take `m = L/x > 0`, since
`x^(p/q) <= x` on this range.
[Signal evaluator](../acl2/signal-bounds.lisp) ·
[Prime powers](../acl2/prime-power-divisibility.lisp) ·
[Euler constant](../lean/LandauWindows/Soft/EulerBounds.lean) ·
[Rational powers](../acl2/rpow-bounds.lisp)

These statements imply the classical recurring-window ceiling rule.
Suppose a zero has real part `beta > theta`. The native uniform
right-half-plane clearance and the `e/4` estimate imply
`beta <= 1`, by taking rational points converging to the putative
zero on a closed half-plane strictly right of one. Choose a rational
exponent `theta'` with `theta <= theta' < beta`, and a rational
`C' > max(0,C)`. Choose `cap` strictly between
`max(251,252−beta)` and `252−theta'`, and approximate the zero's
height by a rational center `h`. A sufficiently small positive
rational slack puts the zero in the interior of the disk. The
arithmetic theorem with exponent `theta'` and ceiling `C'` now
gives a violation on every sufficiently large rational window.

For a real window start `Y` above the threshold, take rational
starts tending to `Y`. A subsequence of the returned addresses
converges inside `[Y,Y^(3/2)]`. The smoothed prime sum is continuous
because it is locally a finite sum of continuous ramps. Passing
to the limit gives `Gz(x) >= C'*x^theta' > C*x^theta`. This
contradicts a ceiling on arbitrarily large real windows.
[Right-half-plane clearance](../acl2/euler-right-clearance.lisp)

## Where PA enters

Encode integers by sign and magnitude, rationals by normalized
numerator–denominator pairs, and finite lists and pairs by natural
number codes. Interval, complex-coordinate and polynomial operations
then use arithmetic operations on these codes. The arithmetic statement
above uses only such codes and the graphs of the certified functions.

The repo's explicit termination measures are `nfix`,
`acl2-count`, `len`, and sums of two such natural-valued terms.
ACL2's recorded termination justifications for the 347 exported
recursive definitions in the theorem's dependency closure also use
natural-valued measures. Structural recursion uses the same size
induction. To interpret a
definition in PA, express its result by a finite evaluation tree on
coded inputs. Induction on the measure gives existence and uniqueness
of the tree's result. An ACL2 induction on a natural-valued measure
has the corresponding PA strong-induction instance obtained by
quantifying over coded inputs of that size. This is the arithmetic
reading behind “roughly PA-strength”. The machine-checked certificate
is in ACL2. The PA reading is a mathematical interpretation of the
fragment, with the classical real and complex comparison given above.
[ACL2 logic](https://www.cs.utexas.edu/~moore/publications/km97a.pdf) ·
[ACL2 induction](https://www.cs.utexas.edu/~moore/publications/acl2-induction-heuristics.pdf)
