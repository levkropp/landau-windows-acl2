import LandauWindows.Soft.LogBounds

namespace LandauWindows.CertificateGeometry

def harmonicValue : ℕ → ℚ
  | 0 => 0
  | count + 1 => (count + 1 : ℚ)⁻¹ + harmonicValue count

theorem harmonicValue_eq (count : ℕ) : harmonicValue count = harmonic count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [harmonicValue, harmonic_succ, ih, add_comm]

def eulerFromLog (count : ℕ) (logarithm : Bounds) : Bounds :=
  ⟨harmonicValue count - logarithm.upper - (count : ℚ)⁻¹,
    harmonicValue count - logarithm.lower⟩

theorem eulerFromLog_sound (count : ℕ) (logarithm : Bounds) (hcount : 0 < count)
    (hlog : logarithm.Contains (Real.log (count : ℝ))) :
    (eulerFromLog count logarithm).Contains Real.eulerMascheroniConstant := by
  have hn : (0 : ℝ) < count := by exact_mod_cast hcount
  have hlower := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant count
  have hupper := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' count
  simp only [Real.eulerMascheroniSeq] at hlower
  simp only [Real.eulerMascheroniSeq', Nat.ne_of_gt hcount, if_false] at hupper
  have hinc := log_increment_bounds hn (show 0 < (count : ℝ) + 1 by positivity)
  have hincUpper : Real.log ((count : ℝ) + 1) - Real.log (count : ℝ) ≤ (count : ℝ)⁻¹ := by
    simpa using hinc.2
  rcases hlog with ⟨hlogLower, hlogUpper⟩
  constructor <;> dsimp [eulerFromLog] <;> push_cast <;>
    rw [harmonicValue_eq] <;> linarith

def eulerBounds (count logCount : ℕ) : Bounds :=
  eulerFromLog count (logBounds count logCount)

theorem eulerBounds_sound (count logCount : ℕ) (hcount : 0 < count)
    (hlogCount : 0 < logCount) :
    (eulerBounds count logCount).Contains Real.eulerMascheroniConstant := by
  apply eulerFromLog_sound count _ hcount
  exact logBounds_sound count logCount (by exact_mod_cast hcount) hlogCount

def eulerCount (epsilon : ℚ) : ℕ := 1 + precisionFuel 2 epsilon

def computedEulerBounds (epsilon : ℚ) : Bounds :=
  eulerBounds (eulerCount epsilon) (logCount (eulerCount epsilon) (epsilon / 2))

theorem computedEulerBounds_sound (epsilon : ℚ) :
    (computedEulerBounds epsilon).Contains Real.eulerMascheroniConstant := by
  apply eulerBounds_sound
  · simp [eulerCount]
  · simp [logCount]

end LandauWindows.CertificateGeometry
