# Prior art survey

Compiled 2026-11-21, by web search plus direct inspection of the Alpöge Lean archive (17.4M lines, downloaded from alpo.ge) and of the sources below. **Gaps are expected; if you know of something missing, please open an issue.** Updated the same day with the verification events of Nov 21 (§2.5).

The question this survey answers: *has anyone produced the explicit, windowed, formalized (and PA-strength-checkable) version of the Landau ceiling step?* Short answer: **no.** The pieces that exist:

## 1. Classical mathematics

| Item | Status | Notes |
|------|--------|-------|
| Landau's theorem (Mellin/Dirichlet transforms of one-signed functions) | ✅ textbook | Landau [Lan05]; Montgomery–Vaughan §15.1 [MV07]; standard tool behind Littlewood's Ω-results |
| One-sided criterion for the exact smoothed error G(x) | ✅ | Stated and proved in Rubinstein's draft (below), Lemma I.1; also in Alpöge's Lean (`ZetaLandau`) |
| **Windowed** one-sided criterion ("the same, on intervals") | ✅ but **non-effective** | Rubinstein draft, Lemma (Part II §1): one page, high-derivative estimates; **no constants** |
| Explicit mirror direction ("zeros verified to height T ⇒ explicit ψ/π bounds") | ✅ classical, unformalized | Kadiri 2005; Büthe 2015/16 ("An analytic method for bounding ψ(x)"); Platt–Trudgian 2021 ("The error term in the prime number theorem"); Rosser–Schoenfeld lineage |
| Explicit *windowed one-sided* direction with constants | ❌ | **This project (T1)** |
| Littlewood oscillation theorems (ψ−x = Ω±(√x·log log log x) etc.) | ✅ classical | The *converse-flavored* statements: bad zero ⇒ big oscillation. Partially formalized (see Lean below) |

**Rubinstein's draft** (the closest prior art, dated 2026-11-21 — the same day this repo was created):
*The Alpöge–Claude proof of the Riemann hypothesis explained for the Riemann zeta function* — "Claude Fable 5.2, Codex Astra 6.2, and Gemini Carbon at the behest of Michael O. Rubinstein", working draft, 164 pp.
https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf
Contains: the one-sided criterion; the windowed lemma with its one-page high-derivative proof (Part II §1); the reduction "RH ⟸ ceilings on recurring windows [Y, Y^{3/2}]"; and a study guide to the rest of the Alpöge argument. It is non-effective (big-O throughout) and covers ζ only. It explicitly cites the Alpöge Lean files for the windowed machinery (e.g. `lean/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean`).

## 2. Formalizations, per system

### Lean 4 / mathlib
- **Loeffler–Stoll, "Formalizing zeta and L-functions in Lean" (2025)**, arXiv:2503.00959 — `riemannZeta`, functional equation, `riemannZeta_ne_zero_of_one_le_re`, a formal **statement** of `RiemannHypothesis`, Dirichlet's theorem. **No explicit formula, no oscillation theorem.** (A third-party mission catalog, prove2.me, states plainly: mathlib provides ζ, the functional equation, von Mangoldt, Γ — "but no explicit formula of any kind.")
- **PrimeNumberTheoremAnd** (Kontorovich, Tao, et al.) — PNT in Lean via Wiener–Ikehara; **explicit error bounds are an announced future goal**, not done. https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- **teorth/IEANTN** — Tao's "Integrated Explicit Analytic Number Theory Network": a dependency graph of explicit-ANT claims as conditional theorem nodes, with Lean-verified edges and auditable evidence metadata (citations, numerics). Early stage. **No oscillation/Landau content, no PA-track — but the natural future home for our certificate nodes.** https://github.com/teorth/IEANTN
- **JohnNDvorak/Littlewood_Proof** — Lean 4, ~54.5k lines, Littlewood's oscillation (ψ−x = Ω±(√x·log log log x)); the *converse-flavored* direction (bad zero ⇒ oscillation). One consolidated `sorry` carrying the deep atoms (Hardy's critical-line zeros + Littlewood). AI co-authored. **Nearest content neighbor: opposite direction, no explicit constants, no windows, no PA-track.**
- **Hubbard, "An explicit prime gap under the Riemann Hypothesis, formalized in Lean" (arXiv:2611.00157)** — Dudek's theorem formalized with a *cited zero-counting bound injected as an explicit hypothesis* (never an axiom) and small-range checks by kernel `decide`. **Methodology precedent** for our certificate/hypothesis-injection discipline.
- **Alpöge archive (Nov 20, 2026)** — contains the full windowed Landau for ζ and for Dirichlet L-functions, but: embedded in a 17.4M-line tree; stated non-explicitly (existential constants throughout); and, for human-auditing purposes, inseparable from the new mathematics around it. The archive was **machine-verified in full on November 21, 2026** (§2.5 below), which makes the *existence* of the formalized windowed lemma certain while leaving all three deficits in place. Our project re-proves this step independently, explicitly, and portably.

### 2.5 The November 21, 2026 verifications of the Alpöge archive

On the day after the announcement, the archive was independently machine-checked in public, several times over:

- **Rubinstein's verification run** — https://mrubinst.github.io/grh-lean-verification — the five headline theorems displayed and explained; a scan of the sources for anything that could introduce an unproved assumption; then four machine checks: a full compile of all 175,187 modules, an axiom audit (the theorems depend only on Lean's three standard axioms), a replay of every module through Lean's kernel, and a check of all 1,484,729 declarations the theorems depend on by **nanoda**, a second, independently written kernel. Scripts and a dated log (including the problems met along the way) are in the repository, so anyone can repeat it.
- **Andrew Sutherland (MIT)** — independent verification files; results, logs, and the exported proof on his MIT page.
- **Elliot Arledge** — an independent rebuild, axiom audit, and nanoda check; receipts on GitHub.
- **Bartosz Naskręcki** — **riemann-rev**, a status dashboard recording who has checked what, with a guide to the route of the proof; the dashboard also lists **Simon DeDeo's** full kernel replay of all 175,187 modules.

What the verifications settle: the archive compiles, the headline theorems depend only on Lean's standard axioms, and two independent kernels accept every relevant declaration. What they do *not* change for this survey: the development's statements of the Landau step remain non-explicit (existential constants, no computable address, no certificate), the tree remains 17.4M lines and unauditable at human scale, and the new mathematics inside remains to be digested. The niche this repo occupies — explicit constants, an independent readable formalization, and a PA-strength track — is unaffected.

### Isabelle / AFP
- Avigad et al. 2006/2007 — first formalized PNT (elementary Selberg proof).
- **Eberl–Paulson, AFP "Prime Number Theorem" (2018)** — analytic (Newman) proof; Mertens theorems with some explicit remainder bounds.
- Eberl, "Nine Chapters of Analytic Number Theory in Isabelle/HOL" (ITP 2019) — ζ, Hurwitz ζ, Dirichlet L-functions, Dirichlet's theorem, PNT.
- **Song–Yao, AFP "Prime Number Theorem with Remainder Term" (2024)** — *first formalized PNT with an explicit error term* `π(x) = Li(x) + O(x·exp(−√(log x)/3653))` plus an explicit zero-free region. **No oscillation/Landau, no windowed anything.** https://isa-afp.org/entries/PNT_with_Remainder.html

### HOL Light
- Harrison — the only analytic PNT in HOL family (~3,600 lines, Newman's proof); Dirichlet's theorem. No ζ-scale theory, no Landau.

### Metamath (set.mm)
- Carneiro — formalized the elementary (Selberg) PNT. No Landau, no explicit formula.

### Coq / Rocq
- Nothing at zeta/PNT scale found; ζ(3) irrationality work exists (Paulson–Li? — the 2025 arXiv paper), with PNT-with-error contributions from that community flowing into Lean via PrimeNumberTheoremAnd.

### ACL2 / nqthm
- Essentially nothing analytic. The number-theory library is recognition-level (`primep`, Tonelli–Shanks, crypto curve primes). ACL2 workshop tallies: 44 of Wiedijk's 100 theorems, with the explicit note that "ACL2 has largely focused on proving theorems rather different from these." **No reals beyond ACL2(r)'s nonstandard extensions, no analysis of ζ, nothing here.** https://acl2.org/doc/index-seo.php?path=5271%2F59986%2F1200%2F20001&xkey=ACL2____NUMBER-THEORY

## 3. The gap, restated

| Property | Rubinstein draft | Alpöge Lean archive | explicit-verification literature | IEANTN / PNT+ | **This project** |
|---|---|---|---|---|---|
| Windowed one-sided criterion | ✅ (ζ) | ✅ (ζ + L-fns) | ❌ (mirror direction only, unwindowed) | ❌ | ✅ |
| Explicit constants / certificate | ❌ | ❌ | mirror direction only | partial (other statements) | ✅ |
| Formalized in a prover | ❌ (paper) | ✅ machine-checked (Nov 21, 2026) — but in-tree, non-explicit, entangled, no PA-track | ❌ | partial (other statements) | ✅ |
| Independent of the Alpöge claim | ✅ | ❌ | ✅ | ✅ | ✅ |
| PA-strength / ACL2-facing | ❌ | ❌ | ❌ | ❌ | ✅ |

## 4. On the reverse-mathematics side (Phase 3 context)

Reverse mathematics of analytic number theory is thin. Tauberian/summability statements have been studied in small cases (Tauber's first theorem and elementary Tauberian companions sit low — around RCA₀); but Landau's oscillation theorem, the explicit formula, and the windowed variants are, to our knowledge as of this writing, **unclassified**. Friedman's "grand conjecture" school expects "ordinary" number theory (RH included, being Π⁰₁) to be provable in EFA — a prediction about the *existence* of weak proofs, which no current technique can exhibit for arguments like this one. Our effective shadow is, as far as we know, the first attempt to place a theorem of this genre explicitly on a PA-strength track.
