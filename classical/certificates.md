# certificates.md — the ceiling-refutation certificate checker

Companion to [`paper.tex`](paper.tex) (Phase 1, target T1). This file
specifies the algorithm of paper §7 as an implementable procedure, with
input/output formats. It is the mathematical interface consumed by the
ACL2 checker (target T3, Phase 4): the transcript format below is what
ACL2 will re-verify with pure rational arithmetic.

Status: working draft of the paper's algorithm. The verified implementation
uses the conservative rational replacements described below.

**Implementation review (2026-11-22):** this remains ideal mathematical
pseudocode. The spacing, window endpoint, and precision formulas below
are generally real, even for rational input. Rational addresses and
budgets require justified rounding before this is an executable certificate
algorithm. ACL2 now certifies a conservative rational window construction,
precision bound, and mesh/search theorem; Lean proves their real-window
interpretation. The actual `Gz` evaluator and window search are now connected
with a proved total precision budget. Integration with the analytic
bounds remains open. See [the arithmetic contract](../docs/arithmetic-contract.md).

---

## 1. Problem statement (machine form)

**Given:** rationals `θ, C, Y, β₁, β₂, γ₁, γ₂, h` such that

- `θ ∈ [1/2, 1)`, `C ≥ 1`, `Y ≥ 20`, `β₁ < β₂`, `γ₁ < γ₂`, `h > 0`;
- the **validity conditions** (V1)–(V5) of paper Definition 5.1 hold
  (all but (V5) are exact rational comparisons; (V5) is decided by
  certified rational interval arithmetic, see §3.2 below);
- the **certified statement** (S1) holds *upstream* (not checked here;
  treated as a hypothesis): the slab
  `Σ = {Re s > 1/2, γ₁ − h < Im s < γ₂ + h}` contains exactly one zero
  of ζ (counted with multiplicity), and it lies in
  `R = [β₁, β₂] × [γ₁, γ₂]`.

**Output:** either `INVALID(reason)`, or a pair `(x, m/2)` with
`x ∈ ℚ ∩ [Y, Y^{3/2}]` and a **transcript** proving

```
G(x) ≥ (C + m/2) · x^θ
```

where `m := Q(j) − C ≥ 1` is the paper's margin (Definition 6.1),
`Q(j) = 3λ^(j+1)/(16·M₁·M₂) − 52.5`.

Theorem 6.2 guarantees the search below never runs to exhaustion on
valid input. If it does, some hypothesis failed — most plausibly (S1).

## 2. Input/output formats

Rationals are pairs of bignums `(num, den)`, `den > 0`, `gcd = 1`.
All real-analytic quantities (square roots, `log`, `exp`) are carried
as **certified rational intervals** `[lo, hi]` (outward-rounded);
a comparison is decided when the intervals are disjoint.

```
INPUT  = (theta, C, Y, beta1, beta2, gamma1, gamma2, h)   # 8 rationals
OUTPUT = OK(x, m_half, transcript) | INVALID(reason)
```

`transcript` is a finite list of records:

```
("log", n, p, [lo, hi])        # certified interval for log p, n = p^a ≤ x
("sum", x, [lo, hi])           # certified interval for G(x)
("power", x, theta, [lo, hi])  # certified interval for x^theta
("compare", [lo1,hi1], [lo2,hi2], verdict)   # each decision
```

Re-verification of a transcript is pure rational arithmetic: sum the
intervals, check the inclusions, check the final comparison. No logs,
no reals. This is the ACL2 core.

## 3. Algorithm

### 3.1 Validity (paper §5.1)

Compute `Γ = γ₂ − γ₁`, `mid = (γ₁+γ₂)/2`. Check, in order:

| # | condition | paper | kind |
|---|-----------|-------|------|
| 1 | `θ < β₁ ≤ β₂ < 1` | (V1) | exact rational |
| 2 | `(252−β₁)² + Γ²/4 < (252−θ)²` | (V2) | exact rational |
| 3 | `(252−β₁)² + Γ²/4 < (252−β₂)² + γ₁²` | (V3) | exact rational |
| 4 | `h ≥ Γ/2 + 17` | (V4) | exact rational |
| 5 | `min(ε_z, δ′, W₁, W₁′) ≥ 10⁻⁶` | (V5) | interval-decided |

(2) and (3) need no square roots — compare sums of squares directly.

### 3.2 Derived quantities (paper §5.2)

Compute certified intervals for:

```
d̄    = sqrt((252−β₁)² + Γ²/4)      M₁ = sqrt(β₂² + γ₂²)
M₂   = sqrt((1−β₁)² + γ₂²)         D_R = sqrt((252−β₂)² + γ₁²)
D_line = sqrt(251.5² + 14.1347²)  (> 251.89)
D_min  = min(D_line, D_R)          λ  = (252−θ)/d̄        (> 1 by (V2))
r_z  = (d̄ + 251.5)/2               ε_z = 251.5 − r_z
W₁   = | |z−1| − r_z |   where |z−1| = sqrt(251² + mid²)
r′   = (d̄ + D_min)/2               δ′ = D_min − r′
W₀ = 1/2   W₀′ = 252 − r′   W₁′ = r′ − 251   t_max = max(|γ₁|,|γ₂|)+252
```

Precision policy: recompute any interval whose width blocks a needed
comparison; the paper's proof shows every comparison is eventually
decided (all quantities are separated by explicit positive margins).

### 3.3 Circle bounds (paper Definition 5.7)

```
B_z  = (N_b(t_max)+2)/min(ε_z, W₁) + 12·ln(t_max+4) + 12
B′   = 5/min(δ′, W₁′) + 12·ln(26) + 12        N_b(t) = 0.6·ln(|t|+2)+2
M_z  = B_z/(W₀W₁) + 1/W₁² + 1.6/W₁ + 1/(M₁M₂ε_z)
M′   = B′/(W₀′W₁′) + 1/(W₁′)² + 1.6/W₁′
```

### 3.4 Thresholds and margin (paper Definition 6.1, Lemma 5.10)

```
j₁ = ceil( log(2·M₁M₂·M_z·d̄) / log(r_z/d̄) )
j₂ = max(0, ceil( log(8·M₁M₂·M′·(252−θ)/λ) / log(r′/d̄) ))
J₀ = ceil( log((16/3)·M₁M₂·(C+54)) / log λ )
J* = max(j₁, j₂, J₀)
U₀ = max(3, (J* + 1/2)/307.5)         Y₀ = exp(U₀)
```

Check `Y ≥ Y₀` (via intervals: `ln Y ≥ U₀`). Compute `U = ln Y` to
within `10⁻³`; set `j = round(307.5·U)` (an integer). Compute a
certified lower bound for `Q(j) = 3λ^(j+1)/(16·M₁M₂) − 52.5` and check
`Q(j) > C + 1`; set `m = Q(j) − C`.

Note the sizes: `λ − 1` can be `~10⁻³`, `j ~ 300·ln Y ~ 10⁵–10⁸`, so
`Q(j) ~ e^(j·ln λ)` — expect astronomically large margins; that is the
point (computability, not competitiveness). Use multiprecision
rationals; every precision budget is explicit in the formulas.

### 3.5 Grid, sieve, search (paper Proposition 6.5)

```
L_h      = (1/2)(ln Y^{3/2})² + 2·ln Y^{3/2} + 1.6 + C + m/2
δ_grid   = m·Y^θ / (4·L_h)
N_grid   = ceil((Y^{3/2} − Y)/δ_grid)
E₀       = Y^{3/2}·( (1/2)(1.5·ln Y)² + 3 )
w        = m·Y^θ / (8·(E₀ + 2(C+m/2)·Y^{3θ/2} + 1))
```

Sieve all prime powers `n ≤ Y^{3/2}` (batch: precompute certified
intervals for `log p`, `p ≤ Y^{3/2}`, to width `w`).

For `k = 0 … N_grid` (with `x_k = min(Y + k·δ_grid, Y^{3/2})`):
evaluate `G(x_k)` and `x_k^θ` by interval arithmetic to width `w`;
if `G(x_k) − (C + m/2)·x_k^θ` is certified `> 0`, output
`OK(x_k, m/2, transcript)` and halt.

If the loop completes: output `INVALID("search exhausted — an input
hypothesis failed, most plausibly (S1)")`.

## 4. Termination and complexity

Paper Proposition 6.5: the grid has
`N_grid ≤ 4·Y^{3/2−θ}·(L_G(Y^{3/2}) + C + 1/2)` points; each
evaluation costs poly(`Y^{3/2}`, `log(1/w)`); the sieve is
poly(`Y^{3/2}`). Total: explicit polynomial in `Y` and the input bit
lengths. On valid input the search provably halts with a violation
(Theorem 6.2); reaching the end of the loop is itself a proof that the
input was invalid.

## 5. What ACL2 (T3) will verify

1. **Transcript checking** (§2 formats): pure rational sums and
   comparisons, terminating by construction.
2. **The threshold arithmetic** (§3.4): integer/rational function
   definitions with explicit loops (logs and exponentials enter only
   through pre-supplied rational intervals, i.e. as pairs of bignums
   with proof obligations of the form "this rational interval contains
   the true value" — those obligations are *hypotheses* in the ACL2
   statement, discharged upstream).
3. **The search bound**: for all inputs in the format above, the loop
   index stays within `N_grid`, and every `OK` output satisfies the
   checked inequality.

The analytic content (zero-isolation, ζ-evaluation correctness) never
enters the checker; it lives in the hypotheses. This is the
hypothesis-injection discipline, and it is what keeps the trusted core
at ACL2 strength (≈PA).

## 6. Sanity checks (planned for `numerics/`)

- Run the validity/threshold pipeline on synthetic certificates:
  a fake "rogue zero" at, say, `0.55 + 30i`, `R = [0.54, 0.56]×[29, 31]`,
  various `θ = 1/2`, `C = 1`: the constants will be terrible
  (`Y₀` astronomically large); the check is that every formula computes
  and every inequality is decided, not that the numbers are useful.
- Cross-check the paper's Appendix arithmetic (the 14 displayed
  inequalities) by exact rational arithmetic.
- Regression: the transcript checker should accept the paper's
  examples and reject perturbed transcripts.
