# Landau Windows

**The "ceiling step" of the Riemann Hypothesis architecture — made explicit, made windowed, made machine-checkable, and (end goal) checkable by the weakest proof systems.**

> **Status (2026-11-21):** created today. Phase 1 core is drafted: the explicit windowed Landau certificate theorem — every constant computable, every existence replaced by a terminating search — is proved in [`classical/paper.tex`](classical/paper.tex), with the certificate algorithm specified in [`classical/certificates.md`](classical/certificates.md). Nothing here proves, claims to prove, or depends on the truth of the Riemann Hypothesis. See [the honesty box](#honesty-box) before citing it.

---

## Why this exists, in one minute

On November 20, 2026, Levent Alpöge announced a proof of the Riemann Hypothesis, formalized in Lean ([his remark](https://alpo.ge/remark.pdf); a 17.4-million-line Lean archive posted in 14 parts at `alpo.ge/lean.tar.gz.part01` … `.part14`). **The archive has since been independently machine-verified** (November 21, 2026): [Rubinstein's verification run](https://mrubinst.github.io/grh-lean-verification) compiled all 175,187 modules, audited the five headline theorems down to Lean's three standard axioms, replayed every module through Lean's kernel, and checked all 1,484,729 relevant declarations with a second, independently written kernel (nanoda) — with scripts and a dated log so anyone can repeat it; Andrew Sutherland (MIT), Elliot Arledge, and Simon DeDeo have posted independent confirmations, tracked on Bartosz Naskręcki's riemann-rev dashboard. The machine checks settle that the archive proves what it claims *from Lean's axioms*; the deep part of the argument is new mathematics that the community will be digesting at human scale for a long time.

But the logical skeleton of the proof is three steps, and only one of them is new:

1. **The mirror** — zeros of ζ come in pairs reflected across the middle line, so it is enough to rule out zeros on the *right*.
2. **The ceiling** — *Landau's theorem*: a one-sided upper bound on the prime-counting error already excludes zeros to the right. A ceiling alone is enough; no floor is needed.
3. **Build the ceiling** — where all ~17 million lines go.

Step 2 is the load-bearing classical interface: it is the whole reason a method that can only build *ceilings* (one-sided bounds, from positivity of integers/lattices) can prove something about *zeros*. It is 1930s-era mathematics, fully trusted, and — this is the remarkable part — **before November 2026 it had never been formalized in any proof system, and even now, with a machine-checked copy sitting inside the 17-million-line Alpöge archive, it has never been written down in the explicit, quantitative form this architecture actually needs, nor in any form that a human can audit in a sitting or a weak system can check.**

This repository takes step 2 and does three things that nobody has done:

1. **Explicit** — state and prove the windowed Landau theorem with fully computable constants (a *certificate*: given an alleged "bad" zero, name an exact place where any claimed ceiling is violated).
2. **Formalized, independently and readably** — machine-check it in Lean in a small, human-auditable form, independent of the 17-million-line Alpöge development (which now contains a machine-checked but non-explicit, non-portable copy of this step).
3. **PA-strength** — package the contrapositive as a finite, purely arithmetic certificate that a *weak* proof system (ACL2 / nqthm) can check, with an end goal of an actual ACL2 proof of this step.

The "windowed" part matters: the Alpöge architecture produces ceilings only on *recurring windows* — long stretches of the number line — not everywhere, and the classical Landau theorem does not directly apply to that. As of today, the windowed version exists only as a non-effective lemma inside [Rubinstein's explanatory draft](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf) (dated the same day this repo was created) and inside Alpöge's Lean archive (now machine-verified — which makes the existence of the formalized lemma certain, but changes none of the three deficits). Neither version has constants; neither can be *run*; neither is checkable by anything weaker than a full-blown proof assistant.

---

## The video, and the exact forty seconds this repo is about

If you are going to watch one explanation of the Alpöge proof, watch this one: **[harttraveller/riemann](https://github.com/harttraveller/riemann)** — the video is in [`assets/full.mp4`](https://github.com/harttraveller/riemann/blob/main/assets/full.mp4), with a written companion, [`explanation.md`](https://github.com/harttraveller/riemann/blob/main/explanation.md), and the full narration script in [`video/narration.py`](https://github.com/harttraveller/riemann/blob/main/video/narration.py).

In the section called **"The plan"**, the narration says this (segment `s3_b`, "Step two: the ceiling"):

> "A dot on the right means a wave that is too loud. And a wave goes up as well as down. Sooner or later, that wave would push the gap up, above the square-root level. Now turn that around. Suppose we could build a ceiling just above the square-root level, and prove the gap never breaks through it. Then no wave can be too loud. So no dot can be on the right. Notice what we did not need: a floor. A ceiling alone is enough. That is a theorem of Edmund Landau, from over a century ago. And it matters, because the method we are about to meet builds ceilings, not floors."

**That step — "a ceiling alone is enough" — is the entire subject of this repository.** The very next segment of the video says: "Step three is everything else. Build the ceiling. … Almost all of the seventeen million lines are spent on this one step." We are not touching step three. We are making the *conversion* — ceiling in, no-bad-zeros out — bulletproof at the weakest possible proof-theoretic strength.

One refinement (explained in the video guide's §4): in this architecture the ceiling is only ever proved on **windows** — recurring stretches of the number line running from some large Y up to Y^1.5 — not for every x. So the Landau step needs a sharpened, *windowed* version. That sharpened version is our main target.

---

## The layman's explanation (no video required)

**The prediction game.** Count the prime numbers up to some height. In the 1790s, Gauss guessed a smooth formula that predicts the count. It is absurdly good: up to a million, the truth is 78,498 primes against a prediction of 78,628 — off by 130, when a million has six digits. Call the difference between truth and prediction **the gap**. The Riemann Hypothesis, in everyday words, says the gap never gets much bigger than the square root of the height you are counting to.

**Waves and dots.** In 1859 Riemann found that the gap is not random noise: it is a sum of pure waves, like a chord played by an orchestra. Each wave comes from a special point ("dot") associated with a function called zeta. Two settings control each wave: its pitch (how fast it wiggles) and its volume (how fast it swells as you count higher). The dot's left-right position sets the volume: a dot sitting further right plays louder.

**The rogue dot.** The Hypothesis says all the dots sit exactly on the middle line of a vertical strip. If even one dot sat to the right, its wave would eventually swell faster than everything else and the gap would break the square-root rule.

**The ceiling trick.** Here is the classical insight this repo is about. A wave goes *up as well as down*. So a loud wave cannot hide: sooner or later it must push the gap up, above the square-root level. Turn that around: if someone can prove that the gap *never* overshoots — a **ceiling**, with **no floor** required — then no loud wave can exist, so no dot can be to the right of the line. That is Landau's theorem, over a century old. It matters because the Alpöge method can only build ceilings (it comes from "a whole number is at least 1", which gives one-sided bounds).

**Windows.** The catch: in the new architecture, the ceiling is only provable in long recurring stretches of the number line — call each one a *window* — rather than everywhere. The sharper, windowed version of Landau's theorem says that is still enough. That sharper version is exactly what we will prove explicitly.

**What "explicit" adds.** The classical theorem is silent on *where* the ceiling gets broken if you assume a rogue dot exists. Our target theorem produces an **address**: given a rigorously certified rogue dot (a rectangle on the map, verified by interval arithmetic to contain a zero of zeta) and any claimed ceiling, we compute a specific window, a specific number x inside it, and a specific margin — and at that x, the prime count provably breaks the ceiling. Checking that one address is *finite arithmetic*: a big addition problem over primes, nothing more. No limits, no infinity, no analysis left at check time. That is what makes the step checkable by the weakest proof systems — and that is the whole game here.

---

## What we are proving, precisely

Full statements live in [`docs/statement.md`](docs/statement.md). The classical core, quoted verbatim from the Alpöge Lean archive (`src/Formalism/StatementU.lean`, with `Gz` from `src/Formalism/StatementOC.lean`):

```lean
-- The smoothed prime-power sum and the error term:
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

-- Landau's one-sided criterion, as stated in the archive:
def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
```

and the windowed form it must be upgraded to (per Rubinstein's draft, Nov 21 2026): *if there are arbitrarily large Y with G(x) ≤ x^θ throughout [Y, Y^{3/2}], then ζ(s) ≠ 0 for Re s > θ.*

The three deliverables:

| ID | Deliverable | Form |
|----|-------------|------|
| **T1** | Explicit windowed Landau: constants computable from the inputs; certificate algorithm | classical paper ([`classical/`](classical/)) |
| **T2** | Lean formalization: a "soft" layer for correctness, an "effective shadow" layer with no choice, explicit witnesses, rational interval arithmetic | Lean project ([`lean/`](lean/)) |
| **T3** | The contrapositive, packaged as a finite certificate checker | ACL2 project ([`acl2/`](acl2/)) |

Plus the L-function (GRH-for-Dirichlet) versions as a stretch goal — the Alpöge archive already carries the windowed L-function machinery in `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`, and our statements should match his where applicable.

---

## Why it's worth doing

1. **No independent, auditable formalization of the oscillation bridge exists.** The only machine-checked copy is embedded in the 17.4M-line Alpöge development — massive, non-explicit (existential constants throughout), and entangled with 17M lines of new mathematics. Outside it: mathlib has ζ, its functional equation, and a statement of RH (Loeffler–Stoll 2025) — but no explicit formula and no Landau-type theorem. Isabelle's AFP has a PNT with an explicit error term (Song–Yao 2024) but no oscillation theorem either. The nearest neighbors (Tao's IEANTN network; a partial, sorry-carrying Lean attempt at *Littlewood's* oscillation) do not cover this; see [`docs/prior-art.md`](docs/prior-art.md).
2. **The windowed explicit version does not exist even on paper.** The windowed lemma appeared (non-effectively) in a draft dated the same day as this repo. No constants, no certificate, no computable content. Without explicit constants, a "verified ceiling" can never be *combined* with Landau numerically — which is precisely what a certificate-verified future needs.
3. **It is the linchpin of the architecture.** The entire "one-sided information suffices" magic — the reason a Chebyshev-style positivity method can prove something about zeros — lives in this step. It is the one classical piece that the new proof cannot work without.
4. **It upgrades a working toolkit.** The mirror-image direction ("zeros verified numerically up to height T ⇒ explicit prime-counting bounds") is the daily bread of computational number theory (Büthe, Platt–Trudgian, Kadiri) and of explicit-verification pipelines — and it, too, has never been formalized. An explicit windowed Landau theorem completes that bridge in the other direction, and slots naturally into claim-network infrastructure like IEANTN.
5. **It is the only seam with a genuine PA-strength track.** Of every piece of the RH architecture, this is the only one whose content is finite arithmetic in disguise — and hence the only one an ACL2-strength system can ever hope to check. Everything else (theta lifts, Galois cohomology, modularity lifting) has no known arithmetic shadow at any proof-theoretic strength.

---

## The end goal: an ACL2-strength proof of the ceiling step

ACL2 (and its ancestor nqthm) is a quantifier-free, choice-free logic of terminating computable functions, with proof-theoretic strength in the neighborhood of Peano Arithmetic. The full RH architecture can never live there: it uses `Classical.choice` tens of thousands of times, quotient constructions, real and complex analysis, and objects with no computable witnesses. Porting Alpöge's 17.4M lines to ACL2 is not a translation problem — it is a re-founding of mathematics.

But the **contrapositive of the ceiling step** is different. Restated as a certificate, it becomes:

```
   INPUT (upstream, not this repo)          THE CERTIFICATE (this repo)              OUTPUT (downstream)
┌────────────────────────────────┐   ┌───────────────────────────────────┐   ┌─────────────────────────┐
│ • a "rogue zero" claim:        │   │ explicit windowed Landau:         │   │ one specific address x, │
│   an isolation rectangle       │──▶│ constants computed from the inputs │──▶│ in a specific window,   │
│   (verified by interval arith.)│   │ + a terminating search procedure  │   │ where the prime count    │
│ • a "ceiling" claim:           │   │ (Phases 1–3: classical paper      │   │ provably breaks the      │
│   constants + windows          │   │   + Lean audit of both)            │   │ ceiling by a margin —    │
└────────────────────────────────┘   └───────────────────────────────────┘   │ finite arithmetic only. │
                                                                             └─────────────────────────┘
                                                       ACL2 checks this final box (Phase 4) ✓
```

All objects in the final box are finite: Λ-sums over primes up to a bound, rational numbers, explicit comparisons. That is exactly the shape of theorem ACL2 was built for. If and when the ceiling side of the architecture is ever verified — by humans, by Lean, by anything — the conversion to "no bad zeros" will already be checkable by a system whose trusted core is a few hundred lines.

The point, in one sentence: **a one-page logical conversion should not need a 17-million-line cathedral to be trusted — we prove it at the strength of arithmetic itself.**

*(To be clear: this is not a scheme to prove RH in ACL2. RH will never be proved in ACL2 by porting any known architecture. This is a scheme to make one load-bearing classical step independently bulletproof, in the only form weak systems can digest.)*

---

## Roadmap

| Phase | Deliverable | Home | Status |
|-------|-------------|------|--------|
| 0 | Statements, prior-art survey, this README | `docs/` | ✅ done (this commit) |
| 1 | Classical paper: explicit windowed Landau with computable constants + certificate algorithm | `classical/` | 🟡 core drafted & compiled ([`paper.pdf`](classical/paper.pdf), 27 pp.); numerics pending |
| 2 | Lean formalization: soft layer + choice-free effective shadow | `lean/` | 🟡 soft layer started: the archive's abstract windowed-Landau cluster lifted wholesale (builds clean against mathlib alone) + `zeta_landau_windowed` **proved** modulo one named hypothesis; axiom audit on every build ([`lean/`](lean/README.md)) |
| 3 | Reverse-math placement of the effective shadow (expect something in the RCA₀–PA range; a genuinely new datapoint for analytic number theory) | `docs/` | ⬜ |
| 4 | ACL2 certificate checker: the finite core, checked | `acl2/` | ⬜ |

Details, success criteria, and risks: [`docs/roadmap.md`](docs/roadmap.md).

## Repository layout

```
landau-windows/
├── README.md            you are here
├── docs/
│   ├── statement.md     the precise target statements (ζ + L-function versions)
│   ├── prior-art.md     what exists, per system and per paper, as of 2026-11-21
│   └── roadmap.md       phases, deliverables, risks
├── classical/           Phase 1: the explicit-constants paper (TeX)
├── lean/                Phase 2: the Lean project (two layers)
└── acl2/                Phase 4: the certificate checker
```

## Prior art in one table

| System / project | ζ / L-functions | PNT | explicit error bounds | oscillation / Landau | PA-track |
|---|---|---|---|---|---|
| Lean (mathlib; Loeffler–Stoll) | ✅ | — | — | ❌ | ❌ |
| Lean (PrimeNumberTheoremAnd; Tao–Kontorovich) | partial | ✅ (Wiener–Ikehara) | announced goal | ❌ | ❌ |
| Lean (teorth/IEANTN — Tao's explicit-ANT claim network) | — | — | nodes planned | ❌ | ❌ |
| Lean (JohnNDvorak/Littlewood_Proof) | partial | — | — | ⚠️ opposite direction, 1 consolidated sorry | ❌ |
| Isabelle AFP (Eberl–Paulson; Song–Yao) | ✅ | ✅ | ✅ (2024, first) | ❌ | ❌ |
| HOL Light (Harrison) | partial | ✅ (analytic) | ❌ | ❌ | ❌ |
| Metamath (Carneiro) | — | ✅ (elementary) | ❌ | ❌ | ❌ |
| ACL2 / nqthm | ❌ | ❌ | ❌ | ❌ | (this repo's end goal) |
| Classical literature | ✅ | ✅ | ✅ (mirror direction: Büthe, Platt–Trudgian, Kadiri) | ⚠️ windowed lemma exists non-effectively (Rubinstein draft, Nov 21 2026) | ❌ |

Full, link-annotated version: [`docs/prior-art.md`](docs/prior-art.md). **If anything in this table is wrong or out of date, please open an issue — that is exactly the kind of correction we want.**

---

## Honesty box

- **The Alpöge claim has been independently machine-verified.** On November 21, 2026 — the day after the announcement and the day this repo was created — the 17.4M-line archive was compiled end-to-end in public, its five headline theorems audited down to Lean's three standard axioms, every module replayed through the kernel, and all 1,484,729 relevant declarations checked by a second, independently written kernel (nanoda): first in [Rubinstein's verification run](https://mrubinst.github.io/grh-lean-verification) (with scripts and a dated log for reproduction), then independently by Andrew Sutherland (MIT), Elliot Arledge, and Simon DeDeo, with the checks tracked on Bartosz Naskręcki's riemann-rev dashboard. This settles the *mechanical* correctness of the development from Lean's axioms; the new mathematics inside it remains to be digested by humans, and nothing in this repository ever depended on the outcome — every target statement here is classical mathematics that was true before November 20, 2026, and useful either way.
- **The windowed lemma is not ours.** The statement (and a one-page non-effective proof, via high-derivative estimates) is due to Rubinstein's explanatory draft of Nov 21, 2026, and appears inside Alpöge's Lean archive. Our contribution is the explicit constants, the certificate form, the *independent and readable* formalization, and the PA-track — not the statement.
- **T1 is drafted with proofs; T2 and T3 are not.** The classical layer ([`classical/paper.tex`](classical/paper.tex), drafted 2026-11-21) has not yet had its first LaTeX compile pass or its scripted numerics check; the Lean (T2) and ACL2 (T3) layers are untouched. Treat everything accordingly.
- **No proof of the Riemann Hypothesis is claimed, attempted, or implied here.**

## Acknowledgments

- Levent Alpöge — the architecture, the remark, and the Lean spec this repo quotes.
- Michael Rubinstein — the windowed lemma and the one-page proof we effectivize; and, separately, the grh-lean-verification run that machine-checked the archive on day two.
- The verification crews — Andrew Sutherland (MIT), Elliot Arledge, Simon DeDeo, and Bartosz Naskręcki's riemann-rev dashboard — for settling the mechanical status of the claim in public, with scripts.
- The reference video repo, [harttraveller/riemann](https://github.com/harttraveller/riemann) — the explanation this README repeatedly points to.
- Edmund Landau, G. H. Hardy, J. E. Littlewood, A. E. Ingham, Pólya — the oscillation theory.
- Montgomery & Vaughan (§15.1), Büthe, Platt–Trudgian, Kadiri — the explicit side.
- The formalization community: Loeffler–Stoll, Eberl, Paulson, Avigad, Carneiro, Song–Yao, Kontorovich–Tao (PNT+ / IEANTN).

## License

MIT — see [LICENSE](LICENSE). (The mathematics is, of course, everyone's.)
