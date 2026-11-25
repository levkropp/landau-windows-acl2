# ACL2 arithmetic proof

**Current status:** 647 books certified with vanilla ACL2 8.5 on SBCL
2.2.9 in Ubuntu/WSL. They contain 3,649 exported theorems, with no `skip-proofs`,
`defaxiom`, trust tags, or ACL2(r). The arithmetic windowed ceiling
reduction is certified in `lw-euler-window-encoded-zero-reduction`.
[Main theorem](euler-window-encoded-zero.lisp)

The [certified book inventory](books.md) lists the results and scope of
every book. The [proof-obligation ledger](../docs/reduction-status.md)
tracks the components through the final arithmetic theorem.

## Current proof path

All evaluators use exact rational arithmetic. Real enclosures are
`(lower . upper)` pairs, and complex samples are rational coordinate pairs.
The window search computes a mesh and certifies positive lower enclosures
of `Gz(x)-C*x^(p/q)` at returned addresses.

1. **Build the coefficient families.** Euler tails and polynomial
   approximations construct the continuation, its logarithmic derivative
   and the normalized coefficient family. For `sigma>3` the normalized
   coefficients agree with the reflected improper Mellin moments to
   explicit error, independently of the chosen Euler chart.
2. **Count and control the interior poles.** A checked circular cover
   fixes the number of interior factors across refinements. A computed
   inner radius contains those factors and separates them from the
   contour. For positive count `M`, a power-sum search finds a large
   reflected interior coefficient in a block of `M` orders.
3. **Use failure of the window search.** A computed threshold puts the
   block and the two preceding orders in the kernel concentration band.
   Failure then bounds the three-term Mellin expression on the same
   window. The exterior term has a uniform geometric bound.
4. **Force a violation.** The theorem
   `lw-euler-circle-pair-window-certificate` uses a checked positive-count
   circle and a checked empty real-centered circle. Exact cancellation
   at one and a finite polynomial comparison supply the native real
   coefficient bound. ACL2 computes the threshold and precision, then
   certifies the returned rational address and strict lower enclosure.

The contour constructor selects a radius inside the supplied interval.
A finite factor-count bound gives separation, and a Harnack estimate
gives a shared Euler value floor. A degree-independent slope bound
then gives one patch radius for both charts. The constructor reserves
clearance from the pole at 1 before selecting the model precisions.
A small Euler value strictly inside a checked cover forces its count
to be positive. The test uses the actual factors that give the fixed
count across all fine requests. A positive count supplies arbitrarily
small interior samples. A larger reference model with a certified
interior floor rules them out and certifies an empty checked circle.
The finite eta argument now gives uniform clearance on the positive
real axis and a computed near-real strip in a fixed Euler disk.
Finite Möbius inversion gives a second uniform Euler value floor on
each half-plane `Re(s) >= a > 1`, independent of height.

The real-circle scan uses these bounds to begin with an empty contour
and select either its last empty circle or an adjacent empty and
positive-count pair. In the second case a probe from the positive
circle determines a rational modulation height. The final theorem
computes the threshold and the sample tolerance independently of the
input probe. [Arithmetic and classical interpretation](../docs/acl2-interpretation.md)

## Reproduce

From Windows PowerShell, with an Ubuntu WSL distribution:

```powershell
wsl -d Ubuntu -u root -- bash /mnt/c/Users/Med/landau-windows/acl2/setup-wsl.sh
wsl -d Ubuntu -- bash /mnt/c/Users/Med/landau-windows/acl2/certify-wsl.sh
```

Adjust the checkout path to match your machine. Setup installs `sbcl`
and `acl2-source`, then saves a local runtime under ignored
`acl2/.tools/runtime`. Only setup needs root.

Certification resets the world between books and requires fresh `.cert`
files for all requested books. With no arguments it checks all 647;
individual names can be supplied for focused work. Books run in sequential
batches of at most 12, each with a five-minute process limit. Every certificate
must be newer than the command's single start marker; the combined log is
`acl2/.tools/certify.log`.
Generated certificates and compiled artifacts are not committed.
ACL2's guard-verification warnings concern optimized raw-Lisp execution;
the logical theorems are certified.

A clean run of the default certification command rebuilt all 647 books.
The workspace audit checked the matching inventory, source freshness
and direct dependency order.

## Foundations

The [interpretation](../docs/acl2-interpretation.md) states the quantifiers,
derives the matching classical Euler value and signal, and describes the
arithmetic coding and induction. The Lean shadow's 13 choice-free
theorems are audited separately.
