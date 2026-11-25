# Draft 02 — evidence and adaptations

## The opening

“A proof of the Riemann hypothesis has recently been checked in Lean”
describes the available formal verification evidence. The narration does
not make a claim about the Clay prize or the completion of mathematical
exposition and review.

The formalization was announced by Levent Alpöge on 20 November 2026,
described as developed with Claude. The verification credits below name
independent checkers of that work, not its authors.

- [Michael Rubinstein's independent check](https://mrubinst.github.io/grh-lean-verification/):
  completed compilation, axiom audit, kernel replay and independent Rust-kernel
  checks of the announced formalization, including Mathlib's RH statement.
- [Andrew Sutherland's verification files](https://math.mit.edu/~drew/grh/):
  the exact checked statements, methods, logs and limitations.

The status was checked on 22 November 2026. Recheck the opening before release.

## The foundations argument

- [Mario Carneiro, The Type Theory of Lean](https://github.com/digama0/lean-type-theory):
  Lean has its own dependent type theory. The set-theoretic models of its
  universe hierarchy use inaccessible-cardinal assumptions. Lean is not
  literally ZFC, and such models do not show that each theorem requires
  those assumptions.
- [J. C. Lagarias, An Elementary Problem Equivalent to RH](https://arxiv.org/abs/math/0008177):
  an elementary equivalent formulation. The existence of such a formulation
  does not establish a PA proof of RH or settle the strength of the equivalence.
- [Gödel's incompleteness theorems](https://plato.stanford.edu/entries/goedel-incompleteness/):
  the standard second incompleteness theorem has consistency, effectiveness,
  arithmetic and derivability hypotheses. ZFC proves the consistency of
  first-order PA by constructing a model; this is a relative justification.
- [ACL2 authors' documentation](https://www.cs.utexas.edu/~moore/acl2/):
  ACL2 uses Common Lisp, not Perl. Its logical strength comes from its axioms
  and inference/definition principles, not the implementation language.
  The project's precise arithmetic interpretation remains an obligation.

## Actual reuse of the reference animation

The source repository is [harttraveller/riemann](https://github.com/harttraveller/riemann),
pinned at `3221da1c0c5b450dedfcd7923e829aca7089408b`.
`reference.json` records SHA256 hashes for its six source/data assets.
The build downloads missing pinned assets into ignored `.tools/reference`.

`repo_story.py` **calls the original `S3Plan.mirror` and `S3Plan.ceiling`
methods**. It also uses the original `ZeroMap`, `CeilingPlot`, zero data,
palette and text/card helpers. Surrounding project scenes and narration are
new. The adapter supplies Windows font equivalents and sentence-timed
tiny-voca narration contexts. It preserves the upstream scene methods.
The wave illustrations are schematic; the zero-map heights use the reference data.

The reference files retain their upstream provenance and are not relicensed
as this repository's source. Drafts are local review artifacts. The original
video and its original voice recording are not embedded in the standalone cut.

## Scope

Landau is presented as a natural starting point with a clear input/output,
not as the only component that could be reduced to arithmetic. No proof that
other components require stronger foundations is known or claimed here.
The full ACL2 Landau reduction is explicitly described as in progress.
See the [proof-obligation ledger](../docs/reduction-status.md).
