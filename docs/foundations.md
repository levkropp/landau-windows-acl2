# Why reduce the foundations?

ACL2 certifies the arithmetic version of the **windowed Landau ceiling
theorem**. Its ordinary-arithmetic coding motivates the roughly PA-strength
description. The classical comparison identifies the tested zero regions
and the window witness. [Interpretation](acl2-interpretation.md)

## Same theorem, fewer assumptions

An ambient proof system can be much stronger than a theorem requires. Lean's
dependent type theory has a universe hierarchy; its usual set-theoretic
consistency models use inaccessible cardinals. This is a statement about
the system's foundations, not a claim that each Lean proof requires those
cardinals. Carneiro's [The Type Theory of Lean](https://github.com/digama0/lean-type-theory)
gives the metatheory and its universe-dependent consistency bounds.

If a theorem previously proved in that setting is also proved in arithmetic,
we have reduced the assumptions needed for that theorem. Calling this a
“stronger proof” is reasonable shorthand for stronger foundational economy;
the conclusion itself has not changed.

Our use of Lean is productive: first check the mathematical statement and
its classical proof, then extract and reprove its effective content. A
`#print axioms` report listing only Lean's three standard axioms is a useful
dependency audit. It is **not** a PA-strength certificate: the underlying
type theory, universes, induction, and interpretation still matter.

## RH and arithmetic

RH admits elementary formulations, such as Lagarias's family of inequalities
involving harmonic numbers and divisor sums. See his
[original paper](https://arxiv.org/abs/math/0008177).
An arithmetic formulation does not imply provability in PA. True arithmetic
sentences can be independent of PA, and a translation's equivalence itself
has a proof whose strength must be accounted for.

Accordingly, we do not assert that RH needs inaccessible cardinals, that RH
has a PA proof, or that a proof using advanced analysis cannot be reduced.
The constructive question is: **which parts can we prove with less?** This
project starts with the windowed ceiling-to-zero-free conversion.

## What incompleteness contributes

Under the standard hypotheses of Gödel's second incompleteness theorem, a
consistent, effectively axiomatized theory capable of sufficient arithmetic
cannot prove its own formal consistency. This is not a claim about every
possible formal system or every informal notion of consistency. See the
[Stanford Encyclopedia discussion](https://plato.stanford.edu/entries/goedel-incompleteness/).

ZFC can construct a model of first-order PA and prove its consistency.
That proof is relative to ZFC's assumptions; it does not make ZFC
self-justifying. Reducing a number-theory theorem to PA reduces the
foundational commitment needed for that result.

## The arithmetic certificate

The reduction constructs finite rational enclosures, generates the
contours from encoded zero data, and proves that the bounded window search
succeeds. Encoding its inputs as numbers and using strong induction on the
natural-valued measures gives the PA reading. ACL2 certifies the arithmetic
theorem, and the classical comparison is given as a mathematical proof.
[ACL2 guide](../acl2/README.md) · [Interpretation](acl2-interpretation.md)
