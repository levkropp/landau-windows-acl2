import LandauWindows.Soft.KernelSpatial
import LandauWindows.Soft.MellinIntegrand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace LandauWindows.CertificateGeometry

def mellinSignalSpatialSlope (cap : ℚ) : ℚ := logSignalSpatialSlope cap * expLipschitzCap cap

def mellinSignalSpatialCap (cap : ℚ) : ℚ :=
  2 + |(logSignalBounds 0 1).lower| + |(logSignalBounds 0 1).upper| + mellinSignalSpatialSlope cap * cap

def mellinSpatialSlope (cap sigma height step : ℚ) : ℚ :=
  kernelSpatialCap cap step * mellinSignalSpatialSlope cap +
    mellinSignalSpatialCap cap * kernelSpatialSlope cap sigma step +
      mellinSignalSpatialCap cap * kernelSpatialCap cap step * |height|

def mellinSpatialErrorFactor (cap step : ℚ) : ℚ :=
  1 + kernelSpatialCap cap step + mellinSignalSpatialCap cap +
    mellinSignalSpatialCap cap * kernelSpatialCap cap step

noncomputable def realMellinIntegrand (value : ℝ) (sigma height : ℚ) (index : ℕ) (step : ℚ) : ℂ :=
  ((Formalism.Gz (Real.exp value) * realKernelWeight value sigma index step : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((-(height : ℝ) * value : ℝ) : ℂ))

theorem realMellinIntegrand_rat (value sigma height : ℚ) (index : ℕ) (step : ℚ) :
    realMellinIntegrand value sigma height index step = mellinWeightedValue value sigma height index step := by
  simp only [realMellinIntegrand, realKernelWeight, mellinWeightedValue, mellinKernelValue,
    Rat.cast_neg, Rat.cast_mul]
  congr 2 <;> push_cast <;> ring

theorem mellinSpatial_parameters (cap sigma height step : ℚ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) :
    0 ≤ mellinSignalSpatialSlope cap ∧ 0 ≤ mellinSignalSpatialCap cap ∧
      0 ≤ mellinSpatialSlope cap sigma height step := by
  rcases spatialBounds_parameters cap hcap with ⟨hK, _, hS⟩
  rcases kernelSpatial_parameters cap sigma step hcap hsigma hstep with ⟨hk, hkw⟩
  have hlg : 0 ≤ mellinSignalSpatialSlope cap := mul_nonneg hS (by linarith)
  have hm : 0 ≤ mellinSignalSpatialCap cap := by dsimp [mellinSignalSpatialCap]; positivity
  refine ⟨hlg, hm, ?_⟩
  dsimp [mellinSpatialSlope]
  positivity

theorem mellinSignalSpatialCap_sound (cap : ℚ) (hcap : 0 ≤ cap) {value : ℝ}
    (hv : value ∈ Set.Icc 0 (cap : ℝ)) :
    |Formalism.Gz (Real.exp value)| ≤ (mellinSignalSpatialCap cap : ℝ) := by
  have hzero := logSignalBounds_sound 0 1 (by decide) (by decide)
  norm_num only [Rat.cast_zero] at hzero
  have hG0 : |Formalism.Gz (Real.exp 0)| ≤
      |((logSignalBounds 0 1).lower : ℝ)| + |((logSignalBounds 0 1).upper : ℝ)| := by
    apply abs_le.mpr
    constructor <;> linarith [hzero.1, hzero.2,
      le_abs_self ((logSignalBounds 0 1).upper : ℝ), neg_abs_le ((logSignalBounds 0 1).lower : ℝ),
      abs_nonneg ((logSignalBounds 0 1).lower : ℝ), abs_nonneg ((logSignalBounds 0 1).upper : ℝ)]
  have hdiff := logSignal_spatial_bound cap hcap hv
    (left := value) (right := 0) ⟨le_rfl, by exact_mod_cast hcap⟩
  have hlg : (0 : ℝ) ≤ mellinSignalSpatialSlope cap := by
    exact_mod_cast (mellinSpatial_parameters cap 0 0 1 hcap (by decide) (by decide)).1
  have ht : |Formalism.Gz (Real.exp value)| ≤ |Formalism.Gz (Real.exp value) - Formalism.Gz (Real.exp 0)| +
      |Formalism.Gz (Real.exp 0)| := by
    simpa using abs_add_le (Formalism.Gz (Real.exp value) - Formalism.Gz (Real.exp 0)) (Formalism.Gz (Real.exp 0))
  simp only [sub_zero, abs_of_nonneg hv.1] at hdiff
  have hb := mul_le_mul_of_nonneg_left hv.2 hlg
  dsimp [mellinSignalSpatialSlope] at hb
  push_cast at hb
  simp only [mellinSignalSpatialCap, mellinSignalSpatialSlope, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_abs]
  nlinarith

private theorem kernel_cap_sound (cap sigma step : ℚ) (index : ℕ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) {value : ℝ}
    (hv : value ∈ Set.Icc 0 (cap : ℝ)) :
    0 ≤ realKernelWeight value sigma index step ∧ realKernelWeight value sigma index step ≤ kernelSpatialCap cap step := by
  have hh : (0 : ℝ) ≤ step := by exact_mod_cast hstep
  have hs : (0 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hp : 0 ≤ value ^ index / (index.factorial : ℝ) := div_nonneg (pow_nonneg hv.1 _) (Nat.cast_nonneg _)
  have he : Real.exp (-(sigma : ℝ) * value) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
  have hc : Real.exp (cap : ℝ) ≤ (expLipschitzCap cap : ℝ) := (computedExpBounds_sound cap 1 hcap).2
  have hK : (0 : ℝ) ≤ expLipschitzCap cap := (Real.exp_pos (cap : ℝ)).le.trans hc
  have hb := ((Real.pow_div_factorial_le_exp value hv.1 index).trans (Real.exp_le_exp.mpr hv.2)).trans hc
  constructor
  · exact mul_nonneg (mul_nonneg hh hp) (Real.exp_pos _).le
  · calc _ ≤ (step : ℝ) * (expLipschitzCap cap : ℝ) * 1 := by
          unfold realKernelWeight
          gcongr
      _ = (kernelSpatialCap cap step : ℝ) := by simp [kernelSpatialCap]

private theorem phase_exp_spatial (left right : ℝ) :
    ‖Complex.exp (Complex.I * (left : ℂ)) - Complex.exp (Complex.I * (right : ℂ))‖ ≤ |left - right| := by
  have heq : Complex.exp (Complex.I * (left : ℂ)) - Complex.exp (Complex.I * (right : ℂ)) =
      Complex.exp (Complex.I * (right : ℂ)) * (Complex.exp (Complex.I * ((left - right : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := (left - right) / 2)) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

theorem realMellinIntegrand_spatial_bound (cap sigma height step : ℚ) (index : ℕ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    ‖realMellinIntegrand left sigma height index step - realMellinIntegrand right sigma height index step‖ ≤
      (mellinSpatialSlope cap sigma height step : ℝ) * |left - right| := by
  rcases mellinSpatial_parameters cap sigma height step hcap hsigma hstep with ⟨hlg, hm, _⟩
  rcases kernelSpatial_parameters cap sigma step hcap hsigma hstep with ⟨hk, hkw⟩
  have hg := logSignal_spatial_bound cap hcap hl hr
  have hw := realKernelWeight_spatial_bound cap sigma step index hcap hsigma hstep hl hr
  have hleft := kernel_cap_sound cap sigma step index hcap hsigma hstep hl
  have hright := kernel_cap_sound cap sigma step index hcap hsigma hstep hr
  have hp := phase_exp_spatial (-(height : ℝ) * left) (-(height : ℝ) * right)
  have harg : |-(height : ℝ) * left - -(height : ℝ) * right| = |(height : ℝ)| * |left - right| := by
    rw [← mul_sub, abs_mul, abs_neg]
  rw [harg] at hp
  have h := real_product_phase_error
    (Formalism.Gz (Real.exp left)) (Formalism.Gz (Real.exp right))
    (realKernelWeight left sigma index step) (realKernelWeight right sigma index step)
    (mellinSignalSpatialCap cap) (kernelSpatialCap cap step)
    ((mellinSignalSpatialSlope cap : ℝ) * |left - right|)
    ((kernelSpatialSlope cap sigma step : ℝ) * |left - right|) (|(height : ℝ)| * |left - right|)
    (Complex.exp (Complex.I * ((-(height : ℝ) * left : ℝ) : ℂ)))
    (Complex.exp (Complex.I * ((-(height : ℝ) * right : ℝ) : ℂ)))
    (by exact_mod_cast hm) (by exact_mod_cast hk)
    (mul_nonneg (by exact_mod_cast hlg) (abs_nonneg _))
    (mul_nonneg (by exact_mod_cast hkw) (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (by simpa [mellinSignalSpatialSlope, Rat.cast_mul, mul_assoc] using hg)
    hw (mellinSignalSpatialCap_sound cap hcap hr) hright.1 hright.2 hleft.1 hleft.2
    (by rw [Complex.norm_exp_I_mul_ofReal]) hp
  unfold realMellinIntegrand
  apply h.trans_eq
  simp only [mellinSpatialSlope, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
  ring

end LandauWindows.CertificateGeometry
