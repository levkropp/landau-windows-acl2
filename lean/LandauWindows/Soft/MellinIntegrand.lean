import LandauWindows.Soft.LogSignal
import LandauWindows.Soft.KernelBounds
import LandauWindows.Soft.PhaseBounds

namespace LandauWindows.CertificateGeometry

def mellinSignalCap (value : ℚ) : ℚ :=
  1 + |(logSignalBounds value 1).lower| + |(logSignalBounds value 1).upper|

def mellinKernelCap (value sigma : ℚ) (index : ℕ) (step : ℚ) : ℚ :=
  1 + (kernelWeightBounds value sigma index step 1).upper

def mellinComponentError (error factor : ℚ) : ℚ := error / (3 * (1 + factor))

def mellinSignalError (value sigma : ℚ) (index : ℕ) (step error : ℚ) : ℚ :=
  min 1 (mellinComponentError error (mellinKernelCap value sigma index step))

def mellinKernelError (value error : ℚ) : ℚ := mellinComponentError error (mellinSignalCap value)

def mellinPhaseError (value sigma : ℚ) (index : ℕ) (step error : ℚ) : ℚ :=
  mellinComponentError error (mellinSignalCap value * mellinKernelCap value sigma index step)

def mellinSignal (value sigma : ℚ) (index : ℕ) (step error : ℚ) : ℚ :=
  (logSignalBounds value (mellinSignalError value sigma index step error)).lower

def mellinWeight (value sigma : ℚ) (index : ℕ) (step error : ℚ) : ℚ :=
  (kernelWeightBounds value sigma index step (mellinKernelError value error)).lower

def mellinPhase (value sigma height : ℚ) (index : ℕ) (step error : ℚ) : QComplex :=
  phaseValue (-(height * value)) (mellinPhaseError value sigma index step error)

def qComplexScale (factor : ℚ) (point : QComplex) : QComplex := (factor * point.1, factor * point.2)

theorem qComplexScale_value (factor : ℚ) (point : QComplex) :
    qComplexValue (qComplexScale factor point) = (factor : ℂ) * qComplexValue point := by
  apply Complex.ext <;> simp [qComplexValue, qComplexScale, Complex.mul_re, Complex.mul_im]

def mellinSample (value sigma height : ℚ) (index : ℕ) (step error : ℚ) : QComplex :=
  qComplexScale (mellinSignal value sigma index step error * mellinWeight value sigma index step error)
    (mellinPhase value sigma height index step error)

/-- All fields are rational endpoint/budget comparisons. ACL2 proves
`lw-mellin-sample-check-valid` for the constructor; this check contains no
analytic coefficient bound or assumed successful search. -/
def mellinSampleCheck (value sigma : ℚ) (index : ℕ) (step error : ℚ) : Bool :=
  let m := mellinSignalCap value
  let k := mellinKernelCap value sigma index step
  let ge := mellinSignalError value sigma index step error
  let we := mellinKernelError value error
  let pe := mellinPhaseError value sigma index step error
  decide (1 ≤ m ∧ 1 ≤ k ∧ 0 < ge ∧ ge ≤ 1 ∧ 0 < we ∧ 0 < pe ∧
    (logSignalBounds value ge).upper - (logSignalBounds value ge).lower ≤ ge ∧
    (kernelWeightBounds value sigma index step we).upper - (kernelWeightBounds value sigma index step we).lower ≤ we ∧
    |mellinSignal value sigma index step error| ≤ m ∧
    0 ≤ mellinWeight value sigma index step error ∧ mellinWeight value sigma index step error ≤ k ∧
    k * ge + m * we + m * k * pe ≤ error)

noncomputable def mellinKernelValue (value sigma : ℚ) (index : ℕ) (step : ℚ) : ℝ :=
  (step : ℝ) * (value : ℝ) ^ index * Real.exp (-(sigma : ℝ) * value) / index.factorial

noncomputable def mellinWeightedValue (value sigma height : ℚ) (index : ℕ) (step : ℚ) : ℂ :=
  ((Formalism.Gz (Real.exp value) * mellinKernelValue value sigma index step : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((-(height * value) : ℚ) : ℂ))

theorem mellinWeightedValue_eq (value sigma height : ℚ) (index : ℕ) (step : ℚ) :
    mellinWeightedValue value sigma height index step =
      (step : ℂ) * (Formalism.Gz (Real.exp value) : ℂ) * (value : ℂ) ^ index *
        Complex.exp (-((sigma : ℂ) + (height : ℂ) * Complex.I) * (value : ℂ)) /
          (index.factorial : ℂ) := by
  have heq : -((sigma : ℂ) + (height : ℂ) * Complex.I) * (value : ℂ) =
      ((-(sigma : ℝ) * (value : ℝ) : ℝ) : ℂ) + Complex.I * ((-(height * value) : ℚ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.exp_add, ← Complex.ofReal_exp]
  dsimp [mellinWeightedValue, mellinKernelValue]
  push_cast
  ring

theorem real_product_phase_error (g g₀ w w₀ m k ge we pe : ℝ) (z z₀ : ℂ)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hge : 0 ≤ ge) (hwe : 0 ≤ we) (_hpe : 0 ≤ pe)
    (hg : |g - g₀| ≤ ge) (hw : |w - w₀| ≤ we) (hg₀ : |g₀| ≤ m)
    (hw₀ : 0 ≤ w₀) (hw₀k : w₀ ≤ k) (hwpos : 0 ≤ w) (hwk : w ≤ k)
    (hz : ‖z‖ ≤ 1) (hphase : ‖z - z₀‖ ≤ pe) :
    ‖((g * w : ℝ) : ℂ) * z - ((g₀ * w₀ : ℝ) : ℂ) * z₀‖ ≤ k * ge + m * we + m * k * pe := by
  have heq : ((g * w : ℝ) : ℂ) * z - ((g₀ * w₀ : ℝ) : ℂ) * z₀ =
      (((g - g₀) * w : ℝ) : ℂ) * z + ((g₀ * (w - w₀) : ℝ) : ℂ) * z +
        ((g₀ * w₀ : ℝ) : ℂ) * (z - z₀) := by push_cast; ring
  rw [heq]
  calc _ ≤ (‖(((g - g₀) * w : ℝ) : ℂ) * z‖ + ‖((g₀ * (w - w₀) : ℝ) : ℂ) * z‖) +
          ‖((g₀ * w₀ : ℝ) : ℂ) * (z - z₀)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (|g - g₀| * w * ‖z‖ + |g₀| * |w - w₀| * ‖z‖) + |g₀| * w₀ * ‖z - z₀‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hwpos, abs_of_nonneg hw₀]
    _ ≤ (ge * k * 1 + m * we * 1) + m * k * pe := by gcongr
    _ = _ := by ring

/-- Meaning of the constructor's arithmetic checks for the actual weighted
Mellin integrand. Every premise beyond the parameter domain is an exact
rational comparison proved by the ACL2 constructor theorem. -/
theorem mellinSample_sound (value sigma height : ℚ) (index : ℕ) (step error : ℚ)
    (hvalue : 0 ≤ value) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step)
    (hcheck : mellinSampleCheck value sigma index step error = true) :
    ‖mellinWeightedValue value sigma height index step -
      qComplexValue (mellinSample value sigma height index step error)‖ ≤ (error : ℝ) := by
  simp only [mellinSampleCheck, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hm, hk, hge, _, hwe, hpe, hgwidth, hwwidth, hgcap, hwpos, hwcap, hbudget⟩
  have hg := logSignalBounds_sound value (mellinSignalError value sigma index step error) hvalue hge
  have hw := kernelWeightBounds_sound value sigma index step (mellinKernelError value error) hvalue hsigma hstep
  have hc := kernelWeightBounds_sound value sigma index step 1 hvalue hsigma hstep
  have hgwidthR : ((logSignalBounds value (mellinSignalError value sigma index step error)).upper : ℝ) -
      (logSignalBounds value (mellinSignalError value sigma index step error)).lower ≤
      (mellinSignalError value sigma index step error : ℝ) := by exact_mod_cast hgwidth
  have hwwidthR : ((kernelWeightBounds value sigma index step (mellinKernelError value error)).upper : ℝ) -
      (kernelWeightBounds value sigma index step (mellinKernelError value error)).lower ≤
      (mellinKernelError value error : ℝ) := by exact_mod_cast hwwidth
  have hgerr : |Formalism.Gz (Real.exp value) - (mellinSignal value sigma index step error : ℝ)| ≤
      (mellinSignalError value sigma index step error : ℝ) := by
    change |Formalism.Gz (Real.exp value) -
      ((logSignalBounds value (mellinSignalError value sigma index step error)).lower : ℝ)| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hg.1)]
    linarith [hg.2]
  have hwerr : |mellinKernelValue value sigma index step - (mellinWeight value sigma index step error : ℝ)| ≤
      (mellinKernelError value error : ℝ) := by
    change |(step : ℝ) * (value : ℝ) ^ index * Real.exp (-(sigma : ℝ) * value) / index.factorial -
      ((kernelWeightBounds value sigma index step (mellinKernelError value error)).lower : ℝ)| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hw.1)]
    linarith [hw.2]
  have hkernel : 0 ≤ mellinKernelValue value sigma index step := by
    have hv : (0 : ℝ) ≤ value := by exact_mod_cast hvalue
    have hh : (0 : ℝ) ≤ step := by exact_mod_cast hstep
    dsimp [mellinKernelValue]
    positivity
  have hkernelCap : mellinKernelValue value sigma index step ≤ (mellinKernelCap value sigma index step : ℝ) := by
    dsimp [mellinKernelCap, mellinKernelValue]
    push_cast
    linarith [hc.2]
  have hp := phaseValue_exp_bound (-(height * value)) (mellinPhaseError value sigma index step error) hpe
  have hz : ‖Complex.exp (Complex.I * ((-(height * value) : ℚ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.mul_re]
    norm_num
  have hprod := real_product_phase_error
    (Formalism.Gz (Real.exp value)) (mellinSignal value sigma index step error)
    (mellinKernelValue value sigma index step) (mellinWeight value sigma index step error)
    (mellinSignalCap value) (mellinKernelCap value sigma index step)
    (mellinSignalError value sigma index step error) (mellinKernelError value error)
    (mellinPhaseError value sigma index step error)
    (Complex.exp (Complex.I * ((-(height * value) : ℚ) : ℂ)))
    (qComplexValue (mellinPhase value sigma height index step error))
    (by exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hm))
    (by exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hk))
    (by exact_mod_cast hge.le) (by exact_mod_cast hwe.le) (by exact_mod_cast hpe.le)
    hgerr hwerr (by exact_mod_cast hgcap) (by exact_mod_cast hwpos) (by exact_mod_cast hwcap)
    hkernel hkernelCap hz (by simpa only [mellinPhase, norm_sub_rev] using hp)
  have hb : (mellinKernelCap value sigma index step : ℝ) * (mellinSignalError value sigma index step error : ℝ) +
      (mellinSignalCap value : ℝ) * (mellinKernelError value error : ℝ) +
      (mellinSignalCap value : ℝ) * (mellinKernelCap value sigma index step : ℝ) *
        (mellinPhaseError value sigma index step error : ℝ) ≤ (error : ℝ) := by exact_mod_cast hbudget
  simpa [mellinWeightedValue, mellinSample, qComplexScale_value] using hprod.trans hb

end LandauWindows.CertificateGeometry
