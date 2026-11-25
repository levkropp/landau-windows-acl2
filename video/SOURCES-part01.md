# Part One: sources and exact scope

The episode separates a supplied proof, the mathematical meaning of its
symbols, and a general consistency argument. New arithmetic and logical
examples are paired with ACL2 notation. The active review voice is local
tiny-voca M2; the final voice has not been substituted.

## Proofs and models

[Timothy Chow, The Consistency of Arithmetic](https://timothychow.net/consistent.pdf),
especially the discussion of the set-theoretic construction of a PA model,
supports the route from a model to a consistency proof in ZFC. The scene is
a mathematical outline, not an ACL2 formalization of ZFC or of PA soundness.
The clock is a proposed interpretation of zero and successor that already
fails a PA axiom; no full modulo-arithmetic model of PA is asserted.

[J Strother Moore, Proving Theorems about Java and the JVM with ACL2](https://www.cs.utexas.edu/~moore/publications/marktoberdorf-02/main.pdf),
sections 2.3–2.4, gives the formal-proof and inference-rule setting for ACL2.
The [ACL2 quantifier tutorial](https://www.cs.utexas.edu/~moore/acl2/v6-2/QUANTIFIER-TUTORIAL.html)
explains implicit universal quantification and the distinction between syntax
and quantified reasoning. Domain hypotheses remain explicit in the examples.

## Coding and Gödel's theorem

The digit encoder is an original toy example. Its leading marker and the
computation `'(2 0 3) → 1203` illustrate finite coding; the teaching book proves
natural-number output under its input hypotheses. It does not implement a
complete PA proof checker or prove a general encoding equivalence.

[MIT, Gödel's Second Incompleteness Theorem](https://web.mit.edu/24.242/www/2ndIncompleteness.pdf)
states the theorem for consistent, recursively axiomatized extensions of PA
and develops the standard provability conditions. The episode states the
theorem with effective axioms, enough arithmetic, consistency, and the usual
formal consistency sentence. It does not claim that every possible formal
system is unable to prove every sentence informally called its consistency.

The consistency specification requires a **full PA proof checker**, which
is not implemented by this teaching book. The current cut states that
requirement in words rather than presenting an undefined predicate as an
executable function. No PA consistency `defthm` is submitted or claimed.

## Stronger backgrounds and universes

[Benedikt Löwe, Large Cardinals, Lent 2023](https://www.math.uni-hamburg.de/home/loewe/Lent2023/),
especially [lecture two](https://www.math.uni-hamburg.de/home/loewe/Lent2023/L23_LC_II.pdf),
supports the model and consistency-strength discussion. Here inaccessible
means **strongly inaccessible**: uncountable, strong limit, and regular.
The two displayed closure properties use choice in the ambient ZFC setting.
The rank hierarchy is schematic; no proof of the model theorem is developed.
Existence of such a cardinal implies consistency of ZFC, so a consistent
ZFC cannot prove that existence assertion. Nonprovability is not a claim of
nonexistence or inconsistency.

[Mario Carneiro, The Type Theory of Lean, soundness construction](https://github.com/digama0/lean-type-theory/blob/master/soundness.tex)
provides the cited set-theoretic universe model. That source treats Lean 3.
The episode uses it to explain a standard modeling strategy, without claiming
to verify the current Lean kernel or to establish the minimal assumptions
needed by an individual theorem.

## Checked teaching artifacts

[teaching-part01.lisp](teaching-part01.lisp) contains six independently
certified teaching theorems: successor nonzero on naturals, modus ponens,
explosion from contradictory premises, the concrete clock wrap, natural
output of the digit encoder, and its concrete encoding example. The exact
rational comparison preview and the clock/natural-successor distinction
are checked assertions. These results are separate from the Landau books.

Certification artifacts and the log are under ignored
`video/.tools/acl2-part01/` and `video/.tools/certify-part01.log`. The opening
zero-addition example also references Part Zero's checked teaching book.

The current cut shows the complete definitions of `video-clock-next`,
`video-digit-listp`, and `video-encode-digits` in popup cards before using
their names compactly. The source text is extracted directly from this book.
Part Zero's corresponding odd-sum definition is extracted from its own
teaching book. Inputs, relevant primitives, branches, and recursive progress
are explained before the cards fold into function-call badges.

The clock definition has a bottom-left footnote:
“nfix keeps a natural number unchanged and returns zero for anything else.”
This is the behavior specified by the [ACL2 NFIX documentation](https://www.cs.utexas.edu/~moore/acl2/v2-7/NFIX.html).
The `mod` operation in the displayed function takes the remainder.
Narration says “Peano Arithmetic” in full and omits the earlier background
reminder at the end of the model-to-consistency explanation.

The set-theoretic consistency argument, Gödel's theorem, inaccessible-cardinal
model construction, and foundational interpretation of an ACL2 fragment are
mathematical explanations or obligations, not purported results of this small
teaching book. The episode promises neither a full RH proof in PA nor a proof
that some particular RH step cannot be reduced further.
