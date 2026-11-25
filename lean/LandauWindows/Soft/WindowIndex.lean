import LandauWindows.Soft.LogBounds

namespace LandauWindows.CertificateGeometry

/- The arithmetic book constructs an index passing this check. Its rational
inequalities imply the actual real logarithmic kernel window bounds below. -/
def windowIndexCheck (start : ℚ) (index : ℕ) : Bool :=
  let bounds := computedLogBounds start (1 / 1000)
  decide (3 ≤ bounds.lower ∧ 1 ≤ index ∧
    (6061 / 20 : ℚ) * bounds.upper ≤ index ∧ (index : ℚ) ≤ (625 / 2 : ℚ) * bounds.lower)

theorem windowIndexCheck_sound (start : ℚ) (index : ℕ) (hstart : 1 ≤ start)
    (hcheck : windowIndexCheck start index = true) :
    3 ≤ Real.log (start : ℝ) ∧ 1 ≤ index ∧
      (4 / 5 : ℝ) ≤ 250 * Real.log (start : ℝ) / index ∧
      250 * Real.log (start : ℝ) / index ≤ (33 / 40 : ℝ) ∧
      (6 / 5 : ℝ) ≤ 375 * Real.log (start : ℝ) / index ∧
      375 * Real.log (start : ℝ) / index ≤ (31 / 25 : ℝ) ∧
      Set.Icc (88 / 100 : ℝ) (112 / 100 : ℝ) ⊆
        Set.Icc (250 * Real.log (start : ℝ) / index) (375 * Real.log (start : ℝ) / index) := by
  simp only [windowIndexCheck, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hlogLower, hindex, hbandLower, hbandUpper⟩
  have hlog := computedLogBounds_sound start (1 / 1000) hstart
  have hlogLowerR : (3 : ℝ) ≤ (computedLogBounds start (1 / 1000)).lower := by
    exact_mod_cast hlogLower
  have hbandLowerR : (6061 / 20 : ℝ) * (computedLogBounds start (1 / 1000)).upper ≤ index := by
    have h : (((6061 / 20 : ℚ) * (computedLogBounds start (1 / 1000)).upper : ℚ) : ℝ) ≤
        ((index : ℚ) : ℝ) := by exact_mod_cast hbandLower
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at h ⊢
    exact h
  have hbandUpperR : (index : ℝ) ≤ (625 / 2 : ℝ) * (computedLogBounds start (1 / 1000)).lower := by
    have h : ((index : ℚ) : ℝ) ≤
        (((625 / 2 : ℚ) * (computedLogBounds start (1 / 1000)).lower : ℚ) : ℝ) := by
      exact_mod_cast hbandUpper
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at h ⊢
    exact h
  have hindexR : (0 : ℝ) < index := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hindex)
  have hU : (3 : ℝ) ≤ Real.log (start : ℝ) := by linarith [hlog.1]
  have hlower : (6061 / 20 : ℝ) * Real.log (start : ℝ) ≤ index := by linarith [hlog.2]
  have hupper : (index : ℝ) ≤ (625 / 2 : ℝ) * Real.log (start : ℝ) := by linarith [hlog.1]
  have hv1low : (4 / 5 : ℝ) ≤ 250 * Real.log (start : ℝ) / index := by
    apply (le_div_iff₀ hindexR).mpr
    linarith
  have hv1high : 250 * Real.log (start : ℝ) / index ≤ (33 / 40 : ℝ) := by
    apply (div_le_iff₀ hindexR).mpr
    linarith
  have hv2low : (6 / 5 : ℝ) ≤ 375 * Real.log (start : ℝ) / index := by
    apply (le_div_iff₀ hindexR).mpr
    linarith
  have hv2high : 375 * Real.log (start : ℝ) / index ≤ (31 / 25 : ℝ) := by
    apply (div_le_iff₀ hindexR).mpr
    linarith
  refine ⟨hU, hindex, hv1low, hv1high, hv2low, hv2high, ?_⟩
  intro point hpoint
  constructor <;> linarith [hpoint.1, hpoint.2]

end LandauWindows.CertificateGeometry
