/-
T1, soft layer: the existence statement, proved as `t1Soft` below.

The explicit windowed Landau certificate theorem, in the logical shape
fixed by ../docs/statement.md §3, mirroring ../classical/paper.tex:

  * the certificate data and validity conditions (V1)–(V5) of the
    paper's Definition 5.1, with the derived clearance quantities of
    its §5.2 stated as explicit definitions (dbar, r_z, eps_z, D_R,
    D_min, r', delta', W_1, W_1');
  * the certified statement (S1) of the paper's Definition 5.1: the slab
    right of the critical line contains exactly one zero of ζ, and it
    lies in the isolation rectangle;
  * `T1Soft`: the conclusion in the paper's Theorem 6.2, existence form:
    beyond an explicit threshold, every window [Y, Y ^ (3/2)] contains
    an address where the claimed ceiling is violated.

The effective content of the paper — the explicit threshold Y₀
(Definition 6.1: Y₀ = exp U₀ with the j₁, j₂, J₀ machinery), the margin
m = Q(j) − C, and the computed address — is what distinguishes the
paper from this soft statement; attaching those constants field by
field (and then re-proving everything witness-explicitly in `Shadow/`)
is the plan of record (../docs/roadmap.md, Phase 2–3).

Note on simplicity: the paper's (S1) asks for exactly one zero counted
with multiplicity, i.e. a simple zero. Per the paper §8.1, a multiple
zero at a single point is harmless for the argument (the pole residue
scales with the multiplicity, and the lower bound uses multiplicity
≥ 1), so this statement only requires uniqueness of the zero *point*;
the simplicity clause will be added when the order-of-zero API is
wired up, to match the paper verbatim.
-/
import Mathlib
import LandauWindows.Statement
import LandauWindows.Soft.ZetaPoleData

open Complex MeasureTheory Set Filter Topology Formalism

noncomputable section

namespace LandauWindows

/-! ### The paper's absolute constants (§3) -/

/-- The paper's evaluation abscissa `σ` (§3): the least value with
`(σ − θ)/(σ − 2) ≤ e ^ c` for all `θ ∈ (0, 1)`. -/
def sigmaK : ℝ := 252

/-! ### Certificate data and the derived quantities (§5.1–5.2) -/

/-- The isolation rectangle `R` (paper Definition 5.1): rational
vertices in the soft layer; here stated over ℝ. -/
structure IsolationRect where
  /-- left edge `β₁`, strictly right of `θ` -/
  beta1 : ℝ
  /-- right edge `β₂` -/
  beta2 : ℝ
  /-- lower edge `γ₁` -/
  gamma1 : ℝ
  /-- upper edge `γ₂` -/
  gamma2 : ℝ
  deriving DecidableEq

namespace IsolationRect

/-- The height `Γ = γ₂ − γ₁` of the rectangle. -/
def height (R : IsolationRect) : ℝ := R.gamma2 - R.gamma1

/-- The mid-height of the rectangle. -/
def mid (R : IsolationRect) : ℝ := (R.gamma1 + R.gamma2) / 2

/-- `d̄`: the maximum distance from the evaluation point
`z = σ + i·mid` to the rectangle (paper §5.2). -/
def dbar (R : IsolationRect) : ℝ :=
  Real.sqrt ((sigmaK - R.beta1) ^ 2 + (height R) ^ 2 / 4)

/-- `D_R`: the minimum distance from the real point `σ` to the
rectangle (paper §5.2). -/
def D_R (R : IsolationRect) : ℝ :=
  Real.sqrt ((sigmaK - R.beta2) ^ 2 + R.gamma1 ^ 2)

/-- `D_min` of the paper §5.2: the clearance of every zero of ζ from
the real point `σ` (the classical inputs of the paper give
`D_min = min D_line D_R` with `D_line > 251.89`); in this soft
statement the classical part is folded into a hypothesis below and
`D_min` is taken as `min D_line D_R`. -/
def D_line : ℝ := Real.sqrt ((sigmaK - 1 / 2) ^ 2 + (14.1347 : ℝ) ^ 2)

/-- The distance from `σ` to the nearest zero of ζ, soft form. -/
def D_min (R : IsolationRect) : ℝ := min D_line (D_R R)

/-- The second Cauchy radius `r_z` (paper §5.2). -/
def r_z (R : IsolationRect) : ℝ := (dbar R + (sigmaK - 1 / 2)) / 2

/-- The line-zero clearance `ε_z` (paper §5.2). -/
def eps_z (R : IsolationRect) : ℝ := (sigmaK - 1 / 2) - r_z R

/-- The first Cauchy radius `r'` (paper §5.2). -/
def r' (R : IsolationRect) : ℝ := (dbar R + D_min R) / 2

/-- The σ-circle clearance `δ'` (paper §5.2). -/
def delta' (R : IsolationRect) : ℝ := D_min R - r' R

/-- The evaluation point `z = σ + i·mid` (paper §5.2). -/
def zpt (R : IsolationRect) : ℂ := (sigmaK : ℂ) + (mid R) * I

/-- `W₁`: the clearance of the z-circle from the point `1`
(paper §5.2). -/
def W1 (R : IsolationRect) : ℝ := |(‖zpt R - 1‖ : ℝ) - r_z R|

/-- `W₁'`: the clearance of the σ-circle from the point `1`
(paper §5.2). -/
def W1' (R : IsolationRect) : ℝ := r' R - 251

end IsolationRect

/-- The validity conditions (V1)–(V5) of the paper's Definition 5.1,
plus the data ranges, collected. -/
def CertificateValid (θ C : ℝ) (R : IsolationRect) (h : ℝ) : Prop :=
  1 / 2 ≤ θ ∧ θ < 1 ∧ 1 ≤ C
    ∧ R.beta1 ≤ R.beta2 ∧ R.gamma1 ≤ R.gamma2 ∧ 0 < h
    ∧ θ < R.beta1 ∧ R.beta2 < 1                              -- (V1)
    ∧ (sigmaK - R.beta1) ^ 2 + (IsolationRect.height R) ^ 2 / 4
        < (sigmaK - θ) ^ 2                                   -- (V2)
    ∧ (sigmaK - R.beta1) ^ 2 + (IsolationRect.height R) ^ 2 / 4
        < (sigmaK - R.beta2) ^ 2 + R.gamma1 ^ 2               -- (V3)
    ∧ IsolationRect.height R / 2 + 17 ≤ h                    -- (V4)
    ∧ 1 / (10 ^ 6 : ℝ) ≤ min (min (IsolationRect.eps_z R) (IsolationRect.delta' R))
        (min (IsolationRect.W1 R) (IsolationRect.W1' R))      -- (V5)

/-- The certified statement (S1) of the paper's Definition 5.1: the
slab `Σ = {Re s > 1/2, γ₁ − h < Im s < γ₂ + h}` contains exactly one
zero of ζ (as a point; see the header note on simplicity), and it lies
in the rectangle. -/
def ZetaIsolated (R : IsolationRect) (h : ℝ) : Prop :=
  ∃ ρ : ℂ,
    riemannZeta ρ = 0
      ∧ 1 / 2 < ρ.re
      ∧ R.gamma1 - h < ρ.im ∧ ρ.im < R.gamma2 + h
      ∧ R.beta1 ≤ ρ.re ∧ ρ.re ≤ R.beta2
      ∧ R.gamma1 ≤ ρ.im ∧ ρ.im ≤ R.gamma2
      ∧ ∀ ρ' : ℂ, riemannZeta ρ' = 0 → 1 / 2 < ρ'.re
          → R.gamma1 - h < ρ'.im ∧ ρ'.im < R.gamma2 + h
          → ρ' = ρ

/-! ### The theorem statement -/

/-- **T1, soft form (proved as `t1Soft` below).** If the
certificate data are valid (paper Definition 5.1) and the certified
statement (S1) holds, then there is a threshold beyond which every
window `[Y, Y ^ (3/2)]` contains an address `x` at which the claimed
ceiling `Gz x ≤ C x ^ θ` is violated:
beyond the threshold, ceilings and certificate-bearing zeros cannot
both stand.  The paper strengthens this to: the threshold `Y₀` is an
explicit computable function of the data (Definition 6.1), the
violation comes with an explicit margin `m = Q(j) − C ≥ 1`, and the
address is found by a terminating search (Proposition 6.5); those
strengthenings are the effective content planned for `Shadow/`. -/
def T1Soft : Prop :=
  ∀ (θ C : ℝ) (R : IsolationRect) (h : ℝ),
    CertificateValid θ C R h →
    ZetaIsolated R h →
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ x : ℝ, x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)) ∧ C * x ^ θ < Gz x

/-- The certificate reading of T1 (paper §6, "contrapositive"): a
ceiling verified to hold throughout a sufficiently large window, plus
a valid certificate, cannot both be true. -/
def CeilingRefutesCertificate : Prop :=
  ∀ (θ C : ℝ) (R : IsolationRect) (h : ℝ) (Y : ℝ),
    CertificateValid θ C R h →
    ZetaIsolated R h →
    T1Soft →
    (∀ x : ℝ, x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)) → Gz x ≤ C * x ^ θ) →
    ∃ Y₀ : ℝ, Y < Y₀

/-- **T1Soft, proved (soft layer).** Purely logical derivation from the
unconditional windowed Landau lemma: the certified zero has real part
`> θ` (validity (V1) plus the rectangle in (S1)), so if the ceiling
`Gz x ≤ C x ^ θ` held on arbitrarily large windows, the unconditional
lemma would contradict its being a zero.  Hence beyond some threshold
every window contains a violation — the soft form of the paper's
Theorem 6.2 (the explicit constants, margin and computed address are
the effective content for `Shadow/`). -/
theorem t1Soft : T1Soft := by
  intro θ C R h hval Ziso
  obtain ⟨hθhalf, hθ1, hC1, -, -, hpos, hθβ, -⟩ := hval
  have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθhalf
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC1
  obtain ⟨ρ, hρζ, -, -, -, hρβ, -, -, -, -⟩ := Ziso
  have hθρ : θ < ρ.re := lt_of_lt_of_le hθβ hρβ
  by_contra hT1
  push_neg at hT1
  have hceil : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)), Gz x ≤ C * x ^ θ := by
    intro U₀
    obtain ⟨Y, hY, hYx⟩ := hT1 (max U₀ 1)
    exact ⟨Y, le_trans (le_max_left U₀ 1) hY,
      le_trans (le_max_right U₀ 1) hY, hYx⟩
  exact absurd hρζ (zeta_landau_windowed_unconditional hθpos hθ1 hC hceil ρ hθρ)

end LandauWindows

end
