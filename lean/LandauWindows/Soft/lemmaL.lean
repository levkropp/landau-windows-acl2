/-
LIFTED from the Alpoege Lean archive (announced 2026-11-20; independently
machine-verified 2026-11-21; see the repository README, honesty box).
Source file:
  src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean
Changes here: import paths rewritten only (Development...LandauZeroFreeCriterion -> LandauWindows.Soft.PoleData; Development...LandauTheorems.poleData -> LandauWindows.Soft.PoleDataConstruction; Development...LandauTheorems.X -> LandauWindows.Soft.X).
No mathematical content was changed.  Statement hygiene: before freezing,
diff this file against the source.
-/
import LandauWindows.Soft.PoleData
import LandauWindows.Soft.PoleDataConstruction
import LandauWindows.Soft.landauWindow
import LandauWindows.Soft.WindowHypUOfWindowHyp
import LandauWindows.Soft.CharFamilyLFunctionNeZeroOfOneLeRe

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith

end Deduction

end
