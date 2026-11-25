import LandauWindows.Soft.ExpBounds

namespace LandauWindows.CertificateGeometry

def kernelWeightScale (value : ℚ) (index : ℕ) (step : ℚ) : ℚ := step * expTerm value index

def kernelWeightPrecision (value : ℚ) (index : ℕ) (step error : ℚ) : ℚ :=
  error / (1 + kernelWeightScale value index step)

def kernelWeightBounds (value sigma : ℚ) (index : ℕ) (step error : ℚ) : Bounds :=
  let scale := kernelWeightScale value index step
  let bounds := computedExpNegBounds (sigma * value) (kernelWeightPrecision value index step error)
  ⟨scale * bounds.lower, scale * bounds.upper⟩

/-- The constructed rational weight encloses the actual log-variable
Mellin kernel, including the factorial and quadrature step. -/
theorem kernelWeightBounds_sound (value sigma : ℚ) (index : ℕ) (step error : ℚ)
    (hvalue : 0 ≤ value) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) :
    (kernelWeightBounds value sigma index step error).Contains
      ((step : ℝ) * (value : ℝ) ^ index * Real.exp (-(sigma : ℝ) * value) /
        (index.factorial : ℝ)) := by
  have h := computedExpNegBounds_sound (sigma * value)
    (kernelWeightPrecision value index step error) (mul_nonneg hsigma hvalue)
  have hc : (0 : ℝ) ≤ kernelWeightScale value index step := by
    exact_mod_cast mul_nonneg hstep (expTerm_nonneg value index hvalue)
  have heq : (kernelWeightScale value index step : ℝ) * Real.exp (-((sigma * value : ℚ) : ℝ)) =
      (step : ℝ) * (value : ℝ) ^ index * Real.exp (-(sigma : ℝ) * value) /
        (index.factorial : ℝ) := by
    simp only [kernelWeightScale, expTerm_eq, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, neg_mul]
    ring
  rw [← heq]
  constructor
  · simpa only [kernelWeightBounds, Bounds.Contains, Rat.cast_mul] using
      mul_le_mul_of_nonneg_left h.1 hc
  · simpa only [kernelWeightBounds, Bounds.Contains, Rat.cast_mul] using
      mul_le_mul_of_nonneg_left h.2 hc

end LandauWindows.CertificateGeometry
