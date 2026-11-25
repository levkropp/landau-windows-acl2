# Revision five: completed Landau ceiling reduction

Revision five preserves revision four's foundations and credited reference
animations. Its transition, focus, ACL2 explanation and ending now report
the completed result rather than an extraction goal.

The claim is the encoded windowed Landau **ceiling conversion**, proved
in first-order Peano Arithmetic and certified in vanilla ACL2.
The theorem computes a threshold, proves search success
and returns a rational certified violation under the encoded-zero
hypotheses. See [Part Nine's source notes](SOURCES-part09.md) and
[the interpretation](../docs/acl2-interpretation.md).

The [PA manuscript](../classical/pa-paper.pdf), Theorem 15.2, supplies the
direct arithmetic proof; Section 14 derives the finite Mellin quadrature
estimates and the final section gives the classical zeta correspondence.
The checked certificate is in ACL2. The theorem converts a hypothetical
zero into a violation of a proposed ceiling. Establishing that ceiling
in a larger RH proof is a further task. Usual set-theoretic models of Lean's
universes are distinguished from assumptions needed by an individual
theorem.

The upstream opening was rechecked on 24 November 2026 against
[Rubinstein's independent verification record](https://mrubinst.github.io/grh-lean-verification/),
which reports the compile, axiom, kernel-replay and independent-kernel
checks complete. That is evidence about the referenced upstream Lean
formalization, not a new result of this repository.

Animation provenance remains pinned by [reference.json](reference.json).
The final local narration is tiny-voca M2; no API keys or hosted speech
service are used. The video, captions, chapter metadata and transcript are
generated from the same sentence timings and validated before the final
MP4 path is replaced.
