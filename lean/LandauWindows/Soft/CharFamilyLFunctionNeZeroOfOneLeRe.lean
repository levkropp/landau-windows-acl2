/-
LIFTED from the Alpoege Lean archive (announced 2026-11-20; independently
machine-verified 2026-11-21; see the repository README, honesty box).
Source file:
  src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe.lean
Changes here: import paths rewritten only (Development...LandauZeroFreeCriterion -> LandauWindows.Soft.PoleData; Development...LandauTheorems.X -> LandauWindows.Soft.X).
No mathematical content was changed.  Statement hygiene: before freezing,
diff this file against the source.
-/
import LandauWindows.Soft.PoleData

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem charFamily_LFunction_ne_zero_of_one_le_re (F : CharFamily) (i : F.ι) (s : ℂ) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction (F.χ i) s ≠ 0 := by
  haveI := F.nz i
  rcases F.adm i with h | h
  · have key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 →
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      intro M _ ψ hM
      subst hM
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hs
    exact key _ (F.χ i) h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs

end Deduction

end
