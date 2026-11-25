# The precise statements

This file records the exact mathematical statements this project targets, their sources, and their relationship to statements already in the literature and in Alpöge's Lean archive. Quantitative forms marked **DRAFT** will be revised in Phase 1.

## 0. Notation

- `Λ(n)` — the von Mangoldt function: `log p` if `n = p^k` is a prime power, else 0.
- The *smoothed* prime-power sum (the counting convention the Alpöge proof uses):

  `S(x) = Σ_{n ≤ x} Λ(n) · (x/n − 1)`

- The prediction: `x·log x − (1 + γ)·x`, with γ the Euler–Mascheroni constant.
- The **error term**:

  `G(x) = S(x) − x·log x + (1 + γ)·x`

  (Called `Gz` in the Lean archive. Values: G(10⁴) ≈ 1.749, G(10⁶) ≈ 11.04 — the "gap" the video narrates.)

Verbatim from Alpöge's archive (`src/Formalism/StatementOC.lean`):

```lean
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
```

`ζ(s)` is the Riemann zeta function (mathlib's `riemannZeta`); zeros mean nontrivial zeros throughout.

## 1. Landau's one-sided criterion (classical, unwindowed)

**Source:** Landau's theorem on Mellin/Dirichlet transforms of eventually one-signed functions; the standard modern reference is Montgomery–Vaughan, *Multiplicative Number Theory I*, §15.1; as stated for this exact G in Rubinstein's draft (Nov 21, 2026), Lemma "one-sided criterion":

> Let `0 < θ < 1`. If `G(x) ≤ x^θ` for all large `x`, then `ζ(s) ≠ 0` for `Re s > θ`.

**Proof idea (classical):** `H(s) = ∫₁^∞ (x^θ − G(x)) x^{−s−1} dx = 1/(s−θ) − F(s)` has eventually nonnegative integrand, where `F(s)` is built from `ζ'/ζ`; Landau's theorem forces a singularity at the abscissa of convergence, but `H` is holomorphic on real `s > θ` (no real zeros of ζ in (0,1)), so the integral converges for `Re s > θ` and `F` is holomorphic there; a zero of ζ there would be a pole of `F`. ∎

Alpöge's archive states the same theorem with both signs and an explicit constant, `src/Formalism/StatementU.lean`:

```lean
def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
```

(There is also a smoothed variant `ZetaLandauBar` with `Gzbar x = ∫₁² u · Gz(x/u) du`. See the archive.)


**Status (2026-11-22): both statements are proved unconditionally in the Lean
soft layer** (`lean/LandauWindows/Soft/ZetaLandau.lean`). The floor direction
applies `landau_window` to the negated statistic. Its real nonvanishing input
is discharged in `Soft/ZetaReal.lean` by proving zeta < 0 on (0,1) through
fractional-part integral continuation. A real zero would contribute a positive
growing term to `Gz`, invisible to a floor, so this sign fact is substantive.

## 2. The windowed version (the statement the architecture actually needs)

**Source:** Rubinstein's draft (Nov 21, 2026), Lemma "the same, on intervals"; also present in Alpöge's Lean (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`, and the ζ-facing machinery in `src/Formalism/`).

> Let `0 < θ < 1`. If there are arbitrarily large `Y` such that `G(x) ≤ x^θ` for all `x ∈ [Y, Y^{3/2}]`, then `ζ(s) ≠ 0` for `Re s > θ`.

**Proof idea (per Rubinstein):** replace Landau's theorem by an estimate of high derivatives of `F` — "which see only one interval at a time"; a one-page argument (his Part II, §1). The classical kernel is the Pólya/Ingham high-derivative method.

**Why windows:** the Alpöge arithmetic produces the ceiling only on recurring stretches `[Y, Y^1.5]` (see the video guide's §4, step 2). Rubinstein's "Conclusion of step 1" makes the interface explicit:

> To prove the Riemann Hypothesis it suffices to show: for every `ε > 0` there are arbitrarily large `Y` with `G(x) ≤ x^{1/2+ε}` throughout `[Y, Y^{3/2}]`.

This is the *contract* our explicit version must honor: it must accept exactly this kind of input.

## 3. Target T1: the explicit windowed certificate theorem

**Status (2026-11-24): explicit single-zero draft, compiled; mathematical review remains open.** [`classical/paper.tex`](../classical/paper.tex), Theorem 6.2, and [`classical/certificates.md`](../classical/certificates.md) give a conditional certificate formulation. Its tuple is `(θ, C, β₁, β₂, γ₁, γ₂, h)` — a rectangle plus slab half-width — with validity conditions (V1)–(V5) and an upstream-certified statement (S1): the slab `{Re s > 1/2, γ₁−h < Im s < γ₂+h}` contains exactly one zero of ζ, counted with multiplicity, lying in `R`. This is stronger than the isolation-rectangle input (a) below, so it does not establish the full draft T1 on all its stated inputs. The paper specifies `Q(j) = 3λ^(j+1)/(16·M₁·M₂) − 52.5`, with `λ = (252−θ)/d̄`, and a terminating grid search that verifies a returned violation. Its threshold is `Y₀(θ, R, C, h)`, defined in Definition 6.1. General cluster handling and the arithmetic interpretation remain required; see the [proof-obligation ledger](reduction-status.md). The original draft target is:

> **T1 (draft).** There are explicit constants and explicit computable functions such that the following holds. Let `1/2 ≤ θ < 1`. Suppose:
>
> (a) a **zero-isolation certificate** is given: a rectangle `R = [β₁, β₂] × [γ₁, γ₂]` with rational vertices, with `β₁ > θ`, certified (by a rigorous interval-arithmetic computation, upstream and not our concern) to contain a zero of ζ;
>
> (b) a **ceiling claim** is given: constants `C ≥ 1` and a window `[Y, Y^{3/2}]` with `Y` at least an explicit threshold `Y₀(θ, R)`.
>
> Then one can explicitly compute an address `x ∈ [Y, Y^{3/2}]` and a margin `m > 0`, both from the data `(θ, R, C, Y)` by terminating algorithms, such that
>
> `G(x) ≥ C · x^θ + m · x^θ`,
>
> and the verification of this inequality at `x` reduces to a finite computation with rational interval arithmetic (a Λ-sum up to an explicit bound, compared against explicit rational bounds).

Contrapositive reading: *if the ceiling claim is true, no certificate-bearing zero can exist in `Re s > θ`* — i.e., windowed Landau, effective. Certificate reading: *a rogue zero and a ceiling cannot both stand; we name where the ceiling breaks*.

Design notes:

- The constants must be **poly-time computable** from the certificate data, and the search for `x` inside the window must have an explicit stopping rule (Phase 1 must show the classical "a wave must go up somewhere" argument can be made constructive enough to yield a search bound).
- The isolation rectangle (a) is deliberately an *input*, not something we produce: zero-finding belongs to interval-arithmetic practitioners; we consume their output. This follows the hypothesis-injection discipline that has precedent in recent Lean explicit number theory.
- The `Y^{3/2}` window length is the architecture's; variants (e.g. `Y^2`, which appears in the L-function side of the archive) should be treated in the same framework, with the dependence on the window exponent tracked explicitly.

The paper's Proposition 6.5 gives an ideal real-grid size bound and a draft
complexity claim; the current ACL2 log/Euler evaluators do not claim time
polynomial in precision bit length. The window exponent is symbolic (paper
Remark 3.4). The fixed slab isolates a single simple zero, so off-line zeros
within about 34 in height cannot be handled individually by that argument.
The ACL2 theorem uses arbitrary-precision rational probes in a compact disk.
It constructs the needed contours without a single-zero slab assumption and
gives a certified rational witness on each sufficiently large window.
[Arithmetic and classical interpretation](acl2-interpretation.md)

## 4. Target T1-L (DRAFT): L-functions / GRH-for-Dirichlet

The archive carries the whole windowed-Landau apparatus for Dirichlet L-functions; verbatim from `src/Formalism/StatementOC.lean`:

```lean
def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)

def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x
```

with one-sided criteria for `Gz − Gχ` in `OCStep` / `OCStepUpper` (same file), and windowed machinery in `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` (`landau_window_contra`, `landau_window_key` — the high-derivative kernel argument). Our stretch goal is the explicit certificate version for the L-function setting, matching the archive's statements where applicable. ζ-first.

## 5. Deliverable forms

| ID | What | Where it will live |
|----|------|-------------------|
| T1 | The theorem of §3, proved classically with explicit constants | `classical/` (paper) |
| T2 | T1 formalized in Lean: (i) a *soft layer* — ordinary mathlib-style, for correctness; (ii) an *effective shadow* — choice-free, explicit witnesses, rational interval arithmetic, by construction interpretable in PA | `lean/` |
| T3 | The arithmetic windowed Landau theorem: checker soundness, guaranteed witness search, and the connection to the analytic statement | `acl2/` |

T3 consumes isolation-rectangle data, ceiling constants, and window endpoints.
Its finite checker verifies a violation at a computed address. The full target
also proves that the search succeeds on the stated inputs and documents the
arithmetic interpretation of the windowed Landau theorem. A checker by itself
does not accomplish the roughly PA-strength reduction. See
[foundational obligations](foundations.md#what-the-acl2-milestone-must-include).
