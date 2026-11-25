# Part Nine: the completed ACL2 reduction

The episode presents `lw-euler-window-encoded-zero-reduction`, frozen at
proof checkpoint `52aec9e915b5d816ff23a66b942500684643f8f6`. The
[PA manuscript](../classical/pa-paper.pdf) proves the encoded reduction
directly in first-order Peano Arithmetic, Theorem 15.2, and supplies the
classical comparison identifying the encoded zero and returned signal
witness. The corresponding development is certified in vanilla ACL2.

## Exact statement and scope

[The theorem](../acl2/euler-window-encoded-zero.lisp) uses rational region
data `251 < cap < 252-p/q`, positive rational slack, rational seed height,
`C>=0`, and the stated natural numerator/positive denominator restrictions.
The nonempty region forces `p/q<1`. An encoded zero means arbitrarily fine
rational probes in the fixed disk, with the native Euler value small at
the requested error. The final theorem needs one such probe at
`error <= zeroSampleRequest/4`.

The positive request and integer threshold are computed independently of
the later offset. For every rational start above the threshold, the actual
bounded search returns a rational address `x`, satisfying `Y<=x` and
`x*x<=Y*Y*Y`, with a strictly positive lower interval endpoint for
`Gz(x)-C*x^(p/q)`. The original ceiling hypothesis remains a separate input
to a larger RH proof architecture. This release proves the windowed ceiling
conversion; it does not claim a full RH proof in Peano Arithmetic.

## Complete source forms displayed

| Snapshot book | Forms |
| --- | --- |
| `euler-window-encoded-zero` | `lw-euler-window-approximate-zerop`; the complete `lw-euler-window-encoded-zero-reduction` theorem, including proof hints, over three numbered pages |
| `euler-continuation` | `lw-complex-euler-continuation-value` |
| `euler-window-circle-pair` | `lw-euler-window-prepare-circles`, `lw-euler-window-zero-sample-request` |
| `euler-window-ceiling-reduction` | `lw-euler-window-ceiling-threshold` |
| `signal-continuity` | `lw-landau-window-search`, `lw-landau-window-address` |

These are seven complete definitions and one theorem form. Imported helper
functions remain in their certified dependency books. The paired contour,
native coefficient, real-axis clearance, right-plane clearance and cluster
arguments are explained through their proved interfaces, not represented
as new miniature implementations in the film.

## Direct Peano Arithmetic proof and classical correspondence

[docs/acl2-interpretation.md](../docs/acl2-interpretation.md) states the
quantifiers, proves the mathematical comparison of the native value with
`Z(s)=riemannZeta₁(s)`, and identifies the returned interval with the
original smoothed prime statistic. Its fixed-truncation argument gives
`|V(s,e)-Z(s)|<=e/4` in the positive half-plane. Continuity, rational density
and compactness connect actual zeros and arbitrarily accurate probes.
The final passage to recurring real windows is part of that comparison.

The manuscript codes the finite data by natural numbers and derives the
required inequalities using ordinary induction. Section 14 establishes
the finite Mellin quadrature estimates. Theorem 15.2 composes the
construction into the threshold and returned rational window witness.
This is a direct mathematical proof in first-order Peano Arithmetic.
The recorded world audit additionally checks 347 exported recursive
definitions in the ACL2 closure, with no measure exceptions.
The [recorded world-audit output](../docs/natural-measure-audit.txt) is
included with the release and matches the hash in the completion audit.
The certificate is machine-checked in ACL2. The manuscript supplies the
Peano Arithmetic proof directly; a complete replay of the ACL2 trace in
a second checker is a different verification route.

## Completion audit and illustrations

[prepare_part_nine.py](prepare_part_nine.py) checks all 647 default book
certificates against their source timestamps, counts 3,649 exported theorem
events, scans for skipped-proof/custom-axiom/trust-tag/attachment events,
and successfully imports the final 558-book certificate closure with the
existing vanilla ACL2 runtime. It freezes the displayed source and
interpretation documents under ignored `.tools/acl2-part09/`. It does not
claim to recertify all books afresh during rendering. The prior clean run,
source hashes and current import are recorded in
[docs/certification-audit.json](../docs/certification-audit.json).

The disk diagrams, local charts, cluster dots, small window `Y=4, x=6`, and
interval `[1/8,3/8]` are explicitly illustrative. They are not asserted
native zero probes or outputs of the enormous final threshold. The film
makes no practical runtime promise. No additional teaching theorem is
substituted for the actual final result.
