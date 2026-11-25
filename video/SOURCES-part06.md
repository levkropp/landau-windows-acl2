# Part Six: explicit scalar kernels and error budgets

This episode constructs rational exponential enclosures and scalar kernel
weights. It then uses separate teaching examples to distinguish evaluation
error, mesh error and an omitted infinite tail. Complex phases and the
oscillating sample now have their own next episode, giving each construction
room for worked examples.

## Actual project constructions

Seventeen function definitions are displayed completely before compact use:

| Snapshot source | Functions shown |
| --- | --- |
| `exp-bounds.lisp` | `lw-exp-term`, `lw-exp-sum`, `lw-exp-band`, `lw-exp-start-index`, `lw-exp-initial-width`, `lw-exp-depth`, `lw-exp-index`, `lw-exp-bounds`, `lw-exp-neg-bounds` |
| `window-index.lisp` | `lw-ceiling-loop`, `lw-ceiling-rational` |
| `rational-window.lisp` | `lw-halving-depth` |
| `kernel-bounds.lisp` | `lw-kernel-weight-scale`, `lw-kernel-weight-precision`, `lw-kernel-weight-bounds` |
| `teaching-part06.lisp` | `video-line-grid`, `video-cell-tolerance` |

The project files are [exp-bounds.lisp](../acl2/exp-bounds.lisp),
[window-index.lisp](../acl2/window-index.lisp),
[rational-window.lisp](../acl2/rational-window.lisp), and
[kernel-bounds.lisp](../acl2/kernel-bounds.lisp). The film's source cards read
their isolated certified copies, rather than changing the project books.

For rational `x >= 0`, `T_k(x)=x^k/k!` is computed by a recurrence and
`S_n(x)` sums indices **zero through n**. A band has endpoints
`[S_n, S_n+2*T_(n+1)]`. The condition `2*x <= n+2` ensures that ratios
between subsequent omitted terms are at most one half. The band bounds
every later finite partial sum. The safe starting index is conservative.

`lw-halving-depth` keeps the width fixed and doubles the tolerance on each
recursive call. That comparison is equivalent to halving the width against
a fixed tolerance. At `x=1`, the starting index is 3 and initial width is
`1/12`; target `1/100` requires depth 4, hence stopping index 7.

The [NIST exponential series](https://dlmf.nist.gov/4.2.E19) identifies the
real exponential. [ExpBounds.lean](../lean/LandauWindows/Soft/ExpBounds.lean)
proves `expBand_sound`, `computedExpBounds_sound` and
`computedExpNegBounds_sound`. The real interpretation is distinct from the
finite arithmetic statement. Positive exponential endpoints at least one
allow reciprocal endpoints to be reversed without increasing full width.

The exact scalar weight is `h*u^k*exp(-sigma*u)/k!`. Its exact rational
scale is `h*T_k(u)`. The primitive decay tolerance is
`error/(1+scale)`, so scaling preserves the requested full-width budget.
[KernelBounds.lean](../lean/LandauWindows/Soft/KernelBounds.lean),
`kernelWeightBounds_sound`, identifies the resulting interval with the real
factorial-normalized quadrature weight, including cell width `h`.

## Checked displayed values

| Call or quantity | Exact result |
| --- | --- |
| `lw-exp-band 1 3` | `(8/3 . 11/4)` |
| `lw-exp-bounds 1 1/100` | `(685/252 . 54801/20160)` |
| `lw-exp-neg-bounds 1 1/10` | `(4/11 . 3/8)` |
| Kernel scale at `u=1/3, k=2, h=1/2` | `1/36` |
| `lw-kernel-weight-bounds 1/3 3 2 1/2 1/10` | `(1/99 . 1/96)`, full width `1/3168` |
| Same weight with tolerance `1/100` | `(560/54801 . 7/685)` |
| Four left rectangles for `f(u)=u` on `[0,1]` | `3/8`, deficit from `1/2` is `1/8` |
| Eight left rectangles | `7/16`, deficit from `1/2` is `1/16` |

## Ten additional teaching theorems

[teaching-part06.lisp](teaching-part06.lisp) certifies
`video-exp-terms`, `video-exp-band-example`,
`video-exp-band-finite-upper`, `video-exp-auto-examples`,
`video-kernel-examples`, `video-line-grid-formula`,
`video-quadrature-examples`, `video-cell-budget`,
`video-decay-tail-sample`, and `video-error-ledger`.
The finite-sum formula and cell-budget result are general arithmetic
theorems; the ledger is a conditional triangle-inequality estimate. Local
proof-support lemmas are separate from these ten exported results.

[prepare_part_six.py](prepare_part_six.py) stages the eight project dependency
books through `kernel-bounds`, then certifies those and the teaching book
with vanilla ACL2 8.5: nine certificates in all. Sources, fingerprints and
the log are under ignored `.tools/acl2-part06/`. The two Lean bridge files
are frozen as source snapshots; this script does not recertify Lean.
No skipped proofs, trust tags, new axioms or ACL2(r) are added. The teaching
theorems are separate from the project's exported theorem count.

## What the quadrature examples do and do not establish

`video-line-grid` is an explicit teaching model of left rectangles for the
line `f(u)=u`. Its results are exact rational equalities. The real area
`1/2` is identified by the elementary triangle/integration calculation.
It is not the project's full Mellin sampler.

A variation bound `|f(u)-f(v)| <= L*|u-v|` gives cell error at most `L*h^2`
and total uniform-grid error at most `L*length*h`. This is a classical
estimate whose hypotheses must be proved for the actual integrand.
The teaching allocation `error/(N+1)` mirrors the project's
`lw-mellin-sum-error` in [mellin-quadrature.lisp](../acl2/mellin-quadrature.lisp).
Its per-cell error is already an error in the weighted contribution.

The tail model is **only** `exp(-u)`: its integral from `T` to infinity is
`exp(-T)`, using the [exponential integral identity](https://dlmf.nist.gov/4.10).
The checked decay band at `T=8` has upper endpoint at most `1/1000`.
For the actual signal, tail bounds also account for `|g(u)| <= A*exp(2u)`,
the polynomial/factorial factor and `sigma>2`; see
[mellin-tail-bounds.lisp](../acl2/mellin-tail-bounds.lisp),
[mellin-integral.lisp](../acl2/mellin-integral.lisp), and their real bridge
[MellinTail.lean](../lean/LandauWindows/Soft/MellinTail.lean).
The model's tail bound is not substituted for the full signal's bound.

Curves and rectangle animations illustrate the mathematics. Floating-point
plotting coordinates are not certificate endpoints. The full Landau
reduction and intended Peano Arithmetic interpretation retain their own
composition and applicability obligations; this film does not declare
those complete.
