# Part Four: sources, certificates, and scope

This episode constructs the repo's smoothed sum and centered statistic from
prime-power recognition, rational logarithm bounds, ramps, and bounds for
Euler's constant. Its definitions match [Statement.lean](../lean/LandauWindows/Statement.lean):

```text
Sz(x) = sum_{1 <= n <= floor(x)} Lambda(n) * (x/n - 1)
Gz(x) = Sz(x) - x*log(x) + (1 + gamma)*x.
```

The input domain used by the final evaluator is rational `x >= 1`, a natural
cutoff covering `x`, and a positive rational primitive width tolerance.

## Certified project sources

[prepare_part_four.py](prepare_part_four.py) copies the dependency closure
of `signal-bounds.lisp` into an isolated tree under
`video/.tools/acl2-part04/`. It certifies all nine project books there, then
the identical copy of [teaching-part04.lisp](teaching-part04.lisp).
The project proof tree is read without being modified. A source fingerprint
caches successful certificates; changed sources trigger recertification.
The build runs this preparation automatically for `--episode 04`.

The source record and log are
`video/.tools/acl2-part04/certified-sources.json` and `certify.log`.
Certificates are beside their snapshot sources under `acl2/` and `video/`
within that isolated tree. Vanilla ACL2 8.5 is used. No `skip-proofs`, trust
tags, or added axioms are introduced by the teaching book.

Twenty newly used functions appear in full source cards before compact use:

| Project source | Functions shown |
| --- | --- |
| [landau-bounds.lisp](../acl2/landau-bounds.lisp) | `lw-rational-power` (natural exponent) |
| [prime-powers.lisp](../acl2/prime-powers.lisp) | `lw-no-divisor`, `lw-primep`, `lw-power-exponent`, `lw-prime-power-search`, `lw-prime-power-data`, `lw-mangoldt-bounds` |
| [rational-window.lisp](../acl2/rational-window.lisp) | `lw-precision-fuel` |
| [log-bounds.lisp](../acl2/log-bounds.lisp) | `lw-log-rectangles`, `lw-log-count`, `lw-log-bounds` |
| [euler-bounds.lisp](../acl2/euler-bounds.lisp) | `lw-harmonic`, `lw-euler-count`, `lw-euler-from-log`, `lw-euler-bounds` |
| [signal-bounds.lisp](../acl2/signal-bounds.lisp) | `lw-ramp`, `lw-signal-count`, `lw-smoothed-sum-bounds`, `lw-gz-bounds-raw`, `lw-interval-width` |

The displayed forms are read from these certified snapshots.
Interval addition, subtraction and scaling were introduced in Part Two.

## Six additional teaching theorems

| Theorem | Result |
| --- | --- |
| `video-prime-power-examples` | The displayed classifications of 16, 13, 6 and 1. |
| `video-log2-four-rectangles` | Four rectangles give `(533/840 . 319/420)`. |
| `video-ramp-padding-zero` | For rational `x >= 1` and positive integer `n >= x`, the ramp is zero. |
| `video-smoothed-example` | The padded interval at `x=9/2` equals `(11/8)` times the log-two interval plus `(1/2)` times the log-three interval. |
| `video-gz-width-budget` | At `x=9/2`, cutoff 9 and primitive tolerance `1/202`, the full interval width is at most `1/4`. |
| `video-gz-two-positive` | The coarse computed interval for `Gz(2)` has positive lower endpoint. |

These supplement the general project theorems imported by the nine books;
they are separate from the project's exported-theorem count. Assertions
also check the exact endpoint pairs displayed in the film.

The coarse `Gz(2)` call is `(lw-gz-bounds-raw 2 2 1)` and returns
`(38114/45045 . 229381/90090)`. The tight width theorem uses the general
bound without evaluating or displaying the much larger endpoint fractions.

## Mathematical interpretation

The [NIST definition of the Mangoldt function](https://dlmf.nist.gov/27.2.E14)
gives `Lambda(p^k)=log(p)` for prime `p` and positive exponent `k`, and zero
otherwise. The weight is the logarithm of the prime base, with no factor of
the exponent. The [NIST logarithm definition](https://dlmf.nist.gov/4.2.E2)
supplies the real area interpretation used for positive inputs. The
[NIST definition of Euler's constant](https://dlmf.nist.gov/5.2.ii) supplies
the harmonic-logarithm limit.

The project's explicit bridges to those real objects are proved in
[PrimePowers.lean](../lean/LandauWindows/Soft/PrimePowers.lean),
[LogBounds.lean](../lean/LandauWindows/Soft/LogBounds.lean),
[EulerBounds.lean](../lean/LandauWindows/Soft/EulerBounds.lean), and
[SignalBounds.lean](../lean/LandauWindows/Soft/SignalBounds.lean).
`gzBoundsRaw_sound` connects the composed interval to `Formalism.Gz`.
The harmonic-logarithm inequality for gamma is a mathematical interpretation
fact; ordinary ACL2 here computes rational endpoints and proves their
arithmetic properties. Gamma is treated as a real constant.

The sum is continuous because, on a fixed bounded range, one fixed finite
cutoff expresses it as a sum of continuous weighted ramps. Corners may
remain. The project continuity argument is in
[SignalWindow.lean](../lean/LandauWindows/Soft/SignalWindow.lean).
Plots and displayed decimal approximations illustrate the real meaning;
certified sample endpoints are exact rationals.

## Width and cutoff bookkeeping

For `x=9/2`, the reduced numerator gives cutoff 9, covering every active
index. Indices 5 through 9 have zero ramp. The term at 1 has zero Mangoldt
weight. The exact real sum is `(11/8)*log(2) + (1/2)*log(3)`.

If every primitive interval has full width at most `epsilon`, the general
bound for the centered statistic is `(count+2)*x*epsilon`. The three costs
are the finite sum, the scaled logarithm, and the scaled gamma interval.
For count 9 and `x=9/2`, the factor is `99/2`. Choosing
`epsilon = (1/4)/(1+99/2) = 1/202` gives width at most `99/404 < 1/4`.
Full width is distinguished from symmetric error radius throughout.

This episode constructs the statistic and its enclosure accuracy. The
fractional-power ceiling term and additional transport estimates have their
own constructions in later episodes. No complete Landau reduction or full
interpretation of ACL2 in Peano Arithmetic is claimed here.
