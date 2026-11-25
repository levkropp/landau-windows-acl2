import LandauWindows.Soft.MellinPartitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace LandauWindows.CertificateGeometry

/-- A coarse global bound sufficient for an effective Mellin tail. -/
theorem Gz_abs_quadratic (value : ℝ) (hvalue : 1 ≤ value) :
    |Formalism.Gz value| ≤ 4 * value ^ 2 := by
  have hnonneg : 0 ≤ value := by linarith
  have hzero : realSmoothedSum 0 ⌈value⌉₊ = 0 := by simp [realSmoothedSum]
  have hsum := realSmoothedSum_lipschitz value 0 ⌈value⌉₊
  rw [hzero, sub_zero, sub_zero, abs_of_nonneg hnonneg,
    realSmoothedSum_eq_Sz value _ hnonneg (Nat.le_ceil value)] at hsum
  have hspos : 0 ≤ Formalism.Sz value := by
    rw [← realSmoothedSum_eq_Sz value ⌈value⌉₊ hnonneg (Nat.le_ceil value), realSmoothedSum]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (le_max_left _ _) ArithmeticFunction.vonMangoldt_nonneg)
  have hsupper : Formalism.Sz value ≤ (value + 1) * value :=
    (le_abs_self _).trans (hsum.trans (mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hnonneg).le hnonneg))
  have hlogpos := Real.log_nonneg hvalue
  have hlogupper := Real.log_le_self hnonneg
  have hepos : 0 ≤ 1 + Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have heupper : 1 + Real.eulerMascheroniConstant ≤ 2 := by linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  rw [abs_le, Formalism.Gz]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlogupper hnonneg,
    mul_nonneg hnonneg hlogpos, mul_nonneg hepos hnonneg, mul_le_mul_of_nonneg_right heupper hnonneg]

def mellinTailCoefficient (rate : ℚ) (index : ℕ) (mass : ℚ) : ℚ :=
  mass * (index + 1) * (index + 2) * (rate⁻¹) ^ (index + 2)

def mellinTailCutoff (rate : ℚ) (index : ℕ) (mass error : ℚ) : ℚ :=
  1 + (index + 2) / rate + (ceilingRational (2 * mellinTailCoefficient rate index mass / error) : ℚ)

def mellinTailRadius (rate : ℚ) (index : ℕ) (mass cutoff : ℚ) : ℚ :=
  mellinTailCoefficient rate index mass / cutoff

theorem kernel_inverse_square_bound (rate : ℚ) (index : ℕ) (hrate : 0 < rate) {value : ℝ}
    (hvalue : 0 < value) :
    value ^ 2 * realKernelWeight value rate index 1 ≤
      ((index + 1 : ℕ) : ℝ) * (index + 2 : ℕ) / (rate : ℝ) ^ (index + 2) := by
  have ha : (0 : ℝ) < rate := by exact_mod_cast hrate
  have ht := Real.pow_div_factorial_le_exp ((rate : ℝ) * value) (mul_pos ha hvalue).le (index + 2)
  have hF : (0 : ℝ) < (index.factorial : ℝ) := by positivity
  have hF2 : (0 : ℝ) < ((index + 2).factorial : ℝ) := by positivity
  have hpow : (0 : ℝ) < (rate : ℝ) ^ (index + 2) := pow_pos ha _
  have hfact : ((index + 2).factorial : ℝ) = ((index + 2 : ℕ) : ℝ) * (index + 1 : ℕ) * index.factorial := by
    simp only [Nat.factorial_succ, Nat.cast_mul]
    ring
  rw [div_le_iff₀ hF2, mul_pow, hfact] at ht
  have heq : value ^ 2 * realKernelWeight value rate index 1 =
      value ^ (index + 2) / ((index.factorial : ℝ) * Real.exp ((rate : ℝ) * value)) := by
    simp only [realKernelWeight, Rat.cast_one, one_mul, neg_mul, Real.exp_neg, pow_add, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos hF (Real.exp_pos _)) hpow).mpr
  nlinarith [ht]

theorem realMellinIntegrand_inverse_square (sigma height : ℚ) (index : ℕ) (hsigma : 2 < sigma)
    {value : ℝ} (hvalue : 0 < value) :
    ‖realMellinIntegrand value sigma height index 1‖ ≤
      (mellinTailCoefficient (sigma - 2) index 4 : ℝ) / value ^ 2 := by
  have hx : 1 ≤ Real.exp value := Real.one_le_exp hvalue.le
  have hg := Gz_abs_quadratic (Real.exp value) hx
  have hp : 0 ≤ value ^ index / (index.factorial : ℝ) := div_nonneg (pow_nonneg hvalue.le _) (Nat.cast_nonneg _)
  have hk : 0 ≤ realKernelWeight value sigma index 1 := by
    dsimp [realKernelWeight]
    exact mul_nonneg (by simpa using hp) (Real.exp_pos _).le
  have hphase : ‖Complex.exp (Complex.I * ((-(height : ℝ) * value : ℝ) : ℂ))‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal _
  have hnorm : ‖realMellinIntegrand value sigma height index 1‖ ≤
      4 * Real.exp value ^ 2 * realKernelWeight value sigma index 1 := by
    simp only [realMellinIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, hphase,
      mul_one, abs_of_nonneg hk]
    exact mul_le_mul_of_nonneg_right hg hk
  have heq : Real.exp value ^ 2 * Real.exp (-(sigma : ℝ) * value) =
      Real.exp (-((sigma : ℝ) - 2) * value) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hproduct : 4 * Real.exp value ^ 2 * realKernelWeight value sigma index 1 =
      4 * realKernelWeight value (sigma - 2) index 1 := by
    simp only [realKernelWeight, Rat.cast_one, one_mul, Rat.cast_sub, Rat.cast_ofNat]
    calc _ = 4 * (value ^ index / index.factorial) * (Real.exp value ^ 2 * Real.exp (-(sigma : ℝ) * value)) := by ring
      _ = _ := by rw [heq]; ring
  rw [hproduct] at hnorm
  have hi := kernel_inverse_square_bound (sigma - 2) index (by linarith) hvalue
  have hc : 4 * (((index + 1 : ℕ) : ℝ) * (index + 2 : ℕ) / ((sigma - 2 : ℚ) : ℝ) ^ (index + 2)) =
      (mellinTailCoefficient (sigma - 2) index 4 : ℝ) := by
    simp only [mellinTailCoefficient, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Rat.cast_pow, Rat.cast_inv,
      inv_pow, div_eq_mul_inv]
    ring
  apply (le_div_iff₀ (sq_pos_of_pos hvalue)).mpr
  have hmul := mul_le_mul_of_nonneg_left hnorm (sq_nonneg value)
  have hscaled := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4)
  rw [hc] at hscaled
  nlinarith

private theorem realMellinIntegrand_continuousOn_Ioi (cutoff : ℝ) (sigma height : ℚ) (index : ℕ)
    (hcutoff : 0 < cutoff) (hsigma : 0 ≤ sigma) :
    ContinuousOn (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Ioi cutoff) := by
  intro value hv
  let cap : ℚ := (⌈value + 1⌉₊ : ℚ)
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  have hvpos : 0 < value := hcutoff.trans hv
  have hvcap : value < (cap : ℝ) := by
    have h := Nat.le_ceil (value + 1)
    simp only [cap, Rat.cast_natCast]
    linarith
  have hlocal := realMellinIntegrand_continuousOn cap sigma height index hcap hsigma
  exact (hlocal.continuousAt (Icc_mem_nhds hvpos hvcap)).continuousWithinAt

theorem realMellinIntegrand_tail_bound (cutoff : ℝ) (sigma height : ℚ) (index : ℕ)
    (hcutoff : 0 < cutoff) (hsigma : 2 < sigma) :
    IntegrableOn (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Ioi cutoff) ∧
      ‖∫ value in Ioi cutoff, realMellinIntegrand value sigma height index 1‖ ≤
        (mellinTailCoefficient (sigma - 2) index 4 : ℝ) / cutoff := by
  let C : ℝ := mellinTailCoefficient (sigma - 2) index 4
  have hC : 0 ≤ C := by
    dsimp [C, mellinTailCoefficient]
    push_cast
    have hr : (0 : ℝ) < sigma - 2 := by exact_mod_cast (show (0 : ℚ) < sigma - 2 by linarith)
    positivity
  have hmajor : IntegrableOn (fun value : ℝ => C * value ^ (-2 : ℝ)) (Ioi cutoff) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hcutoff).const_mul C
  have hbound : ∀ value ∈ Ioi cutoff, ‖realMellinIntegrand value sigma height index 1‖ ≤ C * value ^ (-2 : ℝ) := by
    intro value hv
    have h := realMellinIntegrand_inverse_square sigma height index hsigma (hcutoff.trans hv)
    simpa only [C, Real.rpow_neg (hcutoff.trans hv).le, Real.rpow_two, div_eq_mul_inv] using h
  have hcont := realMellinIntegrand_continuousOn_Ioi cutoff sigma height index hcutoff (by linarith)
  have hint := hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  refine ⟨hint, ?_⟩
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hmajor (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  apply hnorm.trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hcutoff]
  norm_num [Real.rpow_neg_one, C, div_eq_mul_inv]

theorem mellinTailCutoff_adequate (rate mass error : ℚ) (index : ℕ)
    (hrate : 0 < rate) (hmass : 0 ≤ mass) (herror : 0 < error) :
    0 < mellinTailCutoff rate index mass error ∧
      mellinTailRadius rate index mass (mellinTailCutoff rate index mass error) ≤ error / 2 := by
  have hC : 0 ≤ mellinTailCoefficient rate index mass := by dsimp [mellinTailCoefficient]; positivity
  have hceil := ceilingRational_lower (2 * mellinTailCoefficient rate index mass / error) (by positivity)
  have hR : 0 < mellinTailCutoff rate index mass error := by dsimp [mellinTailCutoff]; positivity
  refine ⟨hR, ?_⟩
  dsimp [mellinTailRadius]
  apply (div_le_iff₀ hR).mpr
  have hb := (div_le_iff₀ herror).mp hceil
  have hRceil : (ceilingRational (2 * mellinTailCoefficient rate index mass / error) : ℚ) ≤
      mellinTailCutoff rate index mass error := by
    dsimp [mellinTailCutoff]
    have hpart : (0 : ℚ) ≤ (index + 2) / rate := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hRceil herror.le]

end LandauWindows.CertificateGeometry
