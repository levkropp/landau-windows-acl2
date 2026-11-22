/-
STATEMENTS — lifted verbatim (modulo the import line) from the Alpöge
Lean archive (announced 2026-11-20; independently machine-verified
2026-11-21; see the repository README, honesty box).  Sources:
  src/Formalism/StatementOC.lean   (Sz, Gz)
  src/Formalism/StatementU.lean     (ZetaLandau, ZetaLandauEps)
Statement hygiene: these are kept byte-identical to the archive (apart
from the import) so that a change of meaning is a one-line diff against
the source.  The archive's L-function-facing statements (Schi, Gchi,
OCStep, ...) are not duplicated here; see ../docs/statement.md §4.
-/
import Mathlib

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction in

/-- The smoothed prime-power sum (counting convention of the Alpöge
proof; the paper's `S`). -/
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

open ArithmeticFunction in

/-- The prime-counting error term (the paper's `G`; the "gap" of the
narration). -/
def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-- Landau's one-sided criterion, in the archive's form (both signs;
existential constants).  The `s₀ = 1` disjunct is the ceiling direction
proved windowed in `LandauWindows.Soft.ZetaWindowed`; the `s₀ = -1`
(mirror) direction needs the functional-equation reflection and is
deferred. -/
def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- The `ε`-relaxed variant of the archive. -/
def ZetaLandauEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

end Formalism
