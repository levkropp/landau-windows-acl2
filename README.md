# Landau Windows

**Vanilla ACL2 certifies the arithmetic windowed Landau ceiling reduction.**
The [interpretation](docs/acl2-interpretation.md) connects the encoded zeros
and rational window witnesses to the classical statement.

The Riemann Hypothesis proof architecture in
[Hart Traveller's explanation](https://github.com/harttraveller/riemann/blob/main/explanation.md)
uses Landau's theorem to turn a one-sided bound on a smoothed prime-counting
error into a zero-free region. The bound is available on recurring windows
`[Y, Y^(3/2)]`.

This project isolates that step. A zeta zero with `Re(s) > theta` forces the
ceiling `G(x) <= C x^theta` to fail on sufficiently large windows. The
effective theorem computes a rational address of a violation and certifies
the strict inequality. The [statement](docs/statement.md) defines the
statistic, hypotheses and L-function target.

## Proof status

| Layer | Result |
|---|---|
| Classical | A draft explicit certificate and search algorithm for an isolated zero. [Paper](classical/paper.pdf) · [Algorithm](classical/certificates.md) |
| Lean | Windowed Landau for zeta, both signs of `ZetaLandau` and `ZetaLandauEps`, and real-strip nonvanishing. The soft-layer audit reports `propext`, `Classical.choice` and `Quot.sound`, with zero sorries. [Lean guide](lean/README.md) |
| Arithmetic shadow | 13 choice-free theorems for interval propagation, a computed mesh and guaranteed bounded search. [Lean guide](lean/README.md) |
| ACL2 | **647 certified books and 3,649 exported theorems.** An encoded zero gives a computed threshold and a certified rational window violation. [ACL2 guide](acl2/README.md) |

From a rational region ACL2 constructs the two circles and computes the
precision at which a small Euler sample forces a violation. The same
construction handles clustered and multiple zeros. [Main theorem](acl2/euler-window-encoded-zero.lisp) ·
[Proof ledger](docs/reduction-status.md) · [Roadmap](docs/roadmap.md)

## Why ACL2

A proof of the interpreted Landau theorem in a weaker foundation would
establish that this step uses fewer foundational assumptions. Lean's
ambient theory supports strong constructions, while ACL2 lets us express
the reduction with terminating arithmetic functions and induction. A precise
PA-strength claim depends on the encoding and its interpretation.

Gödel's second incompleteness theorem helps explain the motivation. Under
its usual hypotheses, a consistent effective theory strong enough for
arithmetic cannot prove its own consistency. ZFC can prove the consistency
of PA. RH itself has arithmetic formulations, and the strength required to
prove it is open. [Foundations and sources](docs/foundations.md)

## Reference video

The original video describes the Landau step as **“A ceiling alone is
enough.”**
[Original video](https://github.com/harttraveller/riemann/blob/main/assets/full.mp4) ·
[Segment `s3_b` in the narration](https://github.com/harttraveller/riemann/blob/main/video/narration.py) ·
[Local video setup](video/README.md)

## Build

```sh
cd lean
lake exe cache get
lake build
```

The Lean toolchain and mathlib revision are pinned. The first cache download
is large. For vanilla ACL2 setup and certification, see the
[ACL2 guide](acl2/README.md).

## Sources and credit

The windowed lemma comes from Michael Rubinstein's
[explanatory draft](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf)
and Levent Alpöge's Lean archive. Lifted files identify their archive paths.
[Reproducible archive verification](https://mrubinst.github.io/grh-lean-verification)

Thanks to the source authors, the mathlib and ACL2 communities, and Hart
Traveller for the reference explanation. The repository is licensed under
[MIT](LICENSE). Third-party tools retain their own licenses.
