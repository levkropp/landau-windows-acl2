/-
LIFTED from the Alpoege Lean archive (announced 2026-11-20; independently
machine-verified 2026-11-21; see the repository README, honesty box).
Source file:
  src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/WindowHypOfRpow.lean and WindowHypUOfWindowHyp.lean
Changes here: assembled: only the three generic (CharFamily-free) lemmas are kept (windowHyp_of_rpow_eventually, windowHypU_of_windowHyp_image, windowHypU_of_windowHyp_fun); the CharFamily-specific theorems (windowHyp_of_rpow, windowHypU_of_windowHyp) are dropped.
No mathematical content was changed.  Statement hygiene: before freezing,
diff this file against the source.
-/
import LandauWindows.Soft.PoleData

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHyp_of_rpow_eventually (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have h2 : 0 < η / 2 := by positivity
  have h1 := (tendsto_rpow_atTop h2).eventually_ge_atTop (K / (η / 2))
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (h1.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₁, fun Y hY => ?_⟩
  obtain ⟨ha, hb⟩ := hY₁ Y hY
  refine ⟨hb, ?_⟩
  have hY0 : 0 < Y := by linarith
  have hl := Real.log_le_rpow_div hY0.le h2
  have hp : 0 ≤ Y ^ (η / 2) := by positivity
  have he : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc K * Real.log Y ≤ K * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hl hK
    _ = K / (η / 2) * Y ^ (η / 2) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha hp
    _ = Y ^ η := he.symm

theorem windowHypU_of_windowHyp_image (a b : ℝ) :
    Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h1
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h2

theorem windowHypU_of_windowHyp_fun (R : ℝ → ℝ) (θ : ℝ) :
    (fun u : ℝ => |Real.exp u| • (R (Real.exp u) * Real.exp u ^ (-θ - 1))) =
      fun u => R (Real.exp u) * Real.exp (-θ * u) := by
  funext u
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end Deduction

end