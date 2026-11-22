/-
LIFTED from the Alpoege Lean archive (announced 2026-11-20; independently
machine-verified 2026-11-21; see the repository README, honesty box).
Source file:
  src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean
Changes here: import paths rewritten only (Development...LandauZeroFreeCriterion -> LandauWindows.Soft.PoleData; Development...LandauTheorems.poleData -> LandauWindows.Soft.PoleDataConstruction; Development...LandauTheorems.X -> LandauWindows.Soft.X).
No mathematical content was changed.  Statement hygiene: before freezing,
diff this file against the source.
-/
import LandauWindows.Soft.PoleData
import LandauWindows.Soft.lemmaL
import LandauWindows.Soft.WindowHypOfRpow

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)

end Deduction

end
