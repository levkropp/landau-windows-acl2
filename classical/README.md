# Windowed Landau manuscripts

## Peano arithmetic manuscript

[LaTeX source](pa-paper.tex) · [Compiled manuscript](pa-paper.pdf)

The manuscript proves the encoded windowed Landau ceiling reduction in
first-order Peano arithmetic. It derives the computed threshold and rational
window witness using finite arithmetic, rational bounds and induction.
Section 14 proves the Mellin quadrature estimates. Theorem 15.2 assembles
the arithmetic proof. The last section gives the classical zeta interpretation.

Run this command twice from this directory to resolve references.

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error pa-paper.tex
~~~

Independent builds with the same pdfLaTeX and fonts produce identical PDFs.

### Reproduce the ACL2Lean trace pilot

ACL2Lean captured all eleven interval-search theorems. The seven selected
induction schemes all measured `acl2-count` of the sample list. The trace also
contains arithmetic solver verdicts without their internal derivations. The
manuscript justifies the interval-search statements directly in PA.
The instrumented prover also certified the final theorem's 558-book closure
and exported its trace. ACL2Lean reconstructed the eleven interval-search
proof trees and stopped on a branch marker inside a literal in the final
book's trace.
[ACL2Lean technical overview](https://github.com/OathTech/ACL2Lean/blob/77455781bfbf1950da1db53b7fde91656c15027d/docs/OVERVIEW.md)

Run from the repository root in Linux or WSL with Git, Make and SBCL.

~~~sh
landau_root="$PWD"
pilot="$(mktemp -d)"
git clone https://github.com/OathTech/ACL2Lean.git "$pilot/ACL2Lean"
cd "$pilot/ACL2Lean"
git checkout 77455781bfbf1950da1db53b7fde91656c15027d
git submodule update --init acl2
make -C acl2 LISP="sbcl --no-sysinit"
OUTDIR="$landau_root/acl2/.tools/pa-acl2lean-traces" \
  bash scripts/capture-proof-log.sh "$landau_root/acl2/interval-search.lisp"
~~~

## Original single-zero manuscript

[LaTeX source](paper.tex) · [Compiled paper](paper.pdf) · [Certificate algorithm](certificates.md)

Theorem 6.2 gives the effective ceiling certificate for an isolated zero.
Section 9 lists the constants and identifies the derived quantities that
require rational enclosures. The certified ACL2 theorem starts with arbitrarily
fine probes in a compact disk and constructs the required contours.
[Arithmetic and classical interpretation](../docs/acl2-interpretation.md)
