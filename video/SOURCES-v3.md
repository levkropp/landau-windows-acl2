# Draft 03 — foundations and the Landau extraction

This version expands the teaching sequence before reusing the original
Landau animations. The fixed screen name is `landau-windows-acl2`; narration
says “Landau Windows ACL Two.” It remains a review draft made while the full
ACL2 reduction is in progress.

## Evidence for the opening

Levent Alpöge announced the formalization on 20 November 2026, describing
the work as developed with Claude. “A proof of RH has been checked in Lean”
refers to the reported checks of the formal statement and proof. It does
not make a claim about the Clay prize or completion of exposition and review.

- [Michael Rubinstein's independent verification](https://mrubinst.github.io/grh-lean-verification/).
- [Andrew Sutherland's statements, verification files and limitations](https://math.mit.edu/~drew/grh/).

## Arithmetic, set theory and consistency

- [Timothy Chow, The Consistency of Arithmetic](https://timothychow.net/consistent.pdf)
  explains PA and the set-theoretic consistency proof: construct the natural
  numbers as a model and use soundness. The draft's number-as-set pictures
  are an introductory illustration of this construction.
- [Jin Wei, A Crash Course on Proof Theory](https://bpb-us-w2.wpmucdn.com/web.sas.upenn.edu/dist/b/845/files/2023/09/Pizza_Talk_2023.pdf)
  states the second incompleteness theorem and its application to PA and ZFC.
- [Gödel's incompleteness theorems, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/goedel-incompleteness/)
  supplies further discussion of the standard effectiveness, arithmetic and
  derivability hypotheses. The video gives intuition and states the theorem;
  it does not present a proof. Its consistency claim is the standard formal
  nonexistence of a contradiction proof, not an informal self-certification claim.

## Inaccessible cardinals and Lean

- [Benedikt Löwe, Large Cardinals, Lent 2023](https://www.math.uni-hamburg.de/home/loewe/Lent2023/),
  especially the opening description and second lecture: an inaccessible
  yields a set-theoretic model; assuming consistency, ZFC cannot prove its
  existence. In the video “inaccessible” means **strongly inaccessible**, so
  the sets of rank below it satisfy ZFC. The implication goes from existence
  to consistency; no equivalence is claimed.
- [Mario Carneiro, The Type Theory of Lean](https://github.com/digama0/lean-type-theory)
  describes Lean's foundation and its universe-dependent consistency models.
  The narration concerns a standard set-theoretic model of Lean's universe
  hierarchy. It does not identify Lean's logic with ZFC or assert that each
  theorem needs inaccessible-cardinal assumptions.
- [Jeffrey C. Lagarias, An Elementary Problem Equivalent to RH](https://arxiv.org/abs/math/0008177)
  gives an elementary equivalent formulation. Having an arithmetic formulation
  does not establish a PA proof, and the strength of the equivalence proof
  must also be accounted for.

The extra cardinal assumption is described as an additional foundational
commitment. The draft does not claim those assumptions are inconsistent.
Reducing assumptions leaves the mathematical conclusion unchanged.

## Project scope and ACL2

- [ACL2 authors' documentation](https://www.cs.utexas.edu/~moore/acl2/).
  ACL2 uses Common Lisp. Logical strength is determined by the axioms and
  proof/definition principles used, not by the programming language.
- [Full-reduction evidence and obligations](../docs/reduction-status.md).
  The target includes a general success proof, explicit witnesses, and the
  mathematical interpretation. The video does not substitute a checker for
  the full theorem, assert an automatic equivalence between ACL2 and PA,
  or assert that Landau is the only part reducible to arithmetic.

## Animation and voice credits

The reference is [harttraveller/riemann](https://github.com/harttraveller/riemann),
pinned by `reference.json`. The `S3Plan.mirror` and `S3Plan.ceiling` methods
are called directly. The reference's zero map, zero data, wave illustrations,
palette and helpers are reused through `repo_story.py`'s font adapter.
The original scene methods are preserved. Surrounding foundation scenes and
all spoken narration are new; the wave illustrations remain schematic.

Tiny-voca's male `M2` voice is generated locally with the model/source pins
in `setup.ps1`. The final MP4 is published at its review path only after
packaging, a full decode, and audio/caption-bound checks complete. English
captions, chapter times, a transcript and a verification report accompany it.

Reference source files retain their upstream provenance and are not
relicensed as this project's code. Rendered drafts and downloaded assets
are local review artifacts; no video has been published externally.
