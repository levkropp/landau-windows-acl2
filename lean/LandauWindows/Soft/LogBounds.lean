import LandauWindows.Soft.CertificateGeometry

/-! Real interpretation of the rational rectangle evaluator in
`acl2/log-bounds.lisp`. The arithmetic implementation needs no real logarithm.
This module proves that its rational endpoints enclose that logarithm. -/

namespace LandauWindows.CertificateGeometry

theorem log_increment_bounds {left right : ℝ} (hleft : 0 < left)
    (hright : 0 < right) :
    (right - left) / right ≤ Real.log right - Real.log left ∧
      Real.log right - Real.log left ≤ (right - left) / left := by
  have hupper := Real.log_le_sub_one_of_pos (div_pos hright hleft)
  have hlower := Real.log_le_sub_one_of_pos (div_pos hleft hright)
  rw [Real.log_div hright.ne' hleft.ne'] at hupper
  rw [Real.log_div hleft.ne' hright.ne'] at hlower
  have hu : right / left - 1 = (right - left) / left := by
    field_simp
  have hl : left / right - 1 = -((right - left) / right) := by
    field_simp
    ring
  rw [hu] at hupper
  rw [hl] at hlower
  exact ⟨by linarith, hupper⟩

def logRectangles (start step : ℚ) : ℕ → Bounds
  | 0 => ⟨0, 0⟩
  | count + 1 =>
      Bounds.add ⟨step / (start + step), step / start⟩
        (logRectangles (start + step) step count)

theorem logRectangles_sound (start step : ℚ) (count : ℕ)
    (hstart : 0 < start) (hstep : 0 ≤ step) :
    (logRectangles start step count).Contains
      (Real.log ((start : ℝ) + count * (step : ℝ)) - Real.log (start : ℝ)) := by
  induction count generalizing start with
  | zero => simp [logRectangles, Bounds.Contains]
  | succ count ih =>
      have hs : (0 : ℝ) < start := by exact_mod_cast hstart
      have hh : (0 : ℝ) ≤ step := by exact_mod_cast hstep
      have hinc := log_increment_bounds hs (show 0 < (start : ℝ) + step by linarith)
      have hfirst : (⟨step / (start + step), step / start⟩ : Bounds).Contains
          (Real.log ((start : ℝ) + step) - Real.log (start : ℝ)) := by
        simpa only [Bounds.Contains, Rat.cast_div, Rat.cast_add, add_sub_cancel_left] using hinc
      have hrest := ih (start + step) (by linarith)
      have hsum := Bounds.add_sound hfirst hrest
      have hend : ((start + step : ℚ) : ℝ) + count * (step : ℝ) =
          (start : ℝ) + (count + 1 : ℕ) * (step : ℝ) := by push_cast; ring
      rw [hend] at hsum
      have heq : Real.log ((start : ℝ) + step) - Real.log (start : ℝ) +
          (Real.log ((start : ℝ) + (count + 1 : ℕ) * (step : ℝ)) -
            Real.log ((start : ℝ) + step)) =
          Real.log ((start : ℝ) + (count + 1 : ℕ) * (step : ℝ)) - Real.log (start : ℝ) := by ring
      simpa only [logRectangles, Rat.cast_add, heq] using hsum

def logBounds (value : ℚ) (count : ℕ) : Bounds :=
  logRectangles 1 ((value - 1) / count) count

theorem logBounds_sound (value : ℚ) (count : ℕ) (hvalue : 1 ≤ value)
    (hcount : 0 < count) : (logBounds value count).Contains (Real.log (value : ℝ)) := by
  have hcountR : (count : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcount)
  have hstep : (0 : ℚ) ≤ (value - 1) / count := div_nonneg (by linarith) (by positivity)
  have h := logRectangles_sound 1 ((value - 1) / count) count (by norm_num) hstep
  have hend : (1 : ℝ) + count * (((value - 1) / count : ℚ) : ℝ) = value := by
    push_cast
    field_simp
    ring
  simpa only [logBounds, Rat.cast_one, Real.log_one, hend, sub_zero] using h

-- ACL2's numerator/denominator precision budget is an ordinary natural.
def precisionFuel (width epsilon : ℚ) : ℕ := width.num.natAbs * epsilon.den

private theorem nonnegative_rat_le_num (value : ℚ) (hvalue : 0 ≤ value) :
    value ≤ (value.num.natAbs : ℚ) := by
  have hnumInt := Rat.num_nonneg.mpr hvalue
  have hnum : (0 : ℚ) ≤ value.num := by exact_mod_cast hnumInt
  have hden : (1 : ℚ) ≤ value.den := by exact_mod_cast value.den_pos
  have habs : (value.num.natAbs : ℚ) = (value.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hnumInt]
  rw [habs]
  calc value = (value.num : ℚ) / value.den := value.num_div_den.symm
    _ ≤ value.num := div_le_self hnum hden

theorem precisionFuel_covers (width epsilon : ℚ) (hw : 0 ≤ width) (he : 0 < epsilon) :
    width ≤ (precisionFuel width epsilon : ℚ) * epsilon := by
  have hn : (1 : ℚ) ≤ epsilon.num := by exact_mod_cast (Rat.num_pos.mpr he)
  have hnum : (0 : ℚ) ≤ width.num.natAbs := by positivity
  have heq : (precisionFuel width epsilon : ℚ) * epsilon = (width.num.natAbs : ℚ) * epsilon.num := by
    dsimp [precisionFuel]
    push_cast
    have h := epsilon.num_div_den
    have hd : (epsilon.den : ℚ) ≠ 0 := by exact_mod_cast epsilon.den_ne_zero
    field_simp at h ⊢
    nlinarith
  rw [heq]
  exact (nonnegative_rat_le_num width hw).trans (by nlinarith)

def logCount (value epsilon : ℚ) : ℕ := 1 + precisionFuel (value - 1) epsilon

def computedLogBounds (value epsilon : ℚ) : Bounds := logBounds value (logCount value epsilon)

theorem computedLogBounds_sound (value epsilon : ℚ) (hvalue : 1 ≤ value) :
    (computedLogBounds value epsilon).Contains (Real.log (value : ℝ)) := by
  apply logBounds_sound value _ hvalue
  simp [logCount]

end LandauWindows.CertificateGeometry
