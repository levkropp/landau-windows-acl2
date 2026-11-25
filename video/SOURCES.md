# Draft 01: sources and claim notes

This is an original review draft made before completion of the full ACL2
Landau reduction. The proof work continues separately. No RH result or
completed ACL2 analytic theorem is claimed.

## Reference and visual continuity

- Hart Traveller, [reference video](https://github.com/harttraveller/riemann/blob/main/assets/full.mp4),
  [narration, segment `s3_b`](https://github.com/harttraveller/riemann/blob/main/video/narration.py),
  and [three-step animation source](https://github.com/harttraveller/riemann/blob/main/video/s3_plan.py).
  The five-word quotation “A ceiling alone is enough” is credited on screen.
  The dark background and color vocabulary recall the reference; the follow-up's
  narration, layouts and animation code are new. Its curves are schematic.
- The optional local combined review copy leaves the reference segment intact
  and appends the new draft. The standalone follow-up contains no original
  footage or voice recording. Neither artifact has been published.

## Foundations

- Mario Carneiro, [The Type Theory of Lean](https://github.com/digama0/lean-type-theory).
  The inaccessible-cardinal point concerns usual consistency models of Lean's
  universe hierarchy. It does not establish that any given Lean theorem requires
  those assumptions, or equate Lean's logic with ZFC.
- Jeffrey C. Lagarias, [An Elementary Problem Equivalent to the Riemann Hypothesis](https://arxiv.org/abs/math/0008177),
  *American Mathematical Monthly* 109 (2002), 534–543. An elementary formulation
  does not establish provability in PA; the strength of the equivalence proof
  also matters.
- [Gödel's incompleteness theorems](https://plato.stanford.edu/entries/goedel-incompleteness/),
  *Stanford Encyclopedia of Philosophy*. The displayed PA non-provability claim
  is conditional on consistency and uses the standard consistency predicate.
  The usual effectiveness, arithmetic and derivability conditions apply.
- The ZFC/PA comparison is relative: ZFC constructs a model of first-order PA
  and proves its consistency. This does not make ZFC self-justifying.
- [ACL2 logic documentation](https://www.cs.utexas.edu/~moore/acl2/v2-0/acl2-doc-2.html).
  “Roughly PA strength” describes the extraction target. The precise
  interpretation of the final book path is a required proof obligation.

## Project evidence

The draft uses the qualitative status in the [reduction ledger](../docs/reduction-status.md)
and [foundations guide](../docs/foundations.md). It omits a live theorem count
so concurrent proof development does not immediately stale it.
Certified evaluators and search are components of the intended theorem.
Analytic coefficient estimates, general-zero applicability, and composition
with a precise arithmetic interpretation remain required.

## Production

Manim Community 0.22.1; tiny-voca male voice `M2`, with the source revision and
model hash pinned by `setup.ps1`. Speech is generated locally. The draft has
selectable English captions and companion SRT/VTT files. The original
reference's speech service is not used for the follow-up.
