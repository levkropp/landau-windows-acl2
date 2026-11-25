import LandauWindows.Soft.ExpBounds

namespace LandauWindows.CertificateGeometry

abbrev QComplex := ℚ × ℚ

def qComplexValue (point : QComplex) : ℂ := ⟨point.1, point.2⟩

def qComplexMul (left right : QComplex) : QComplex :=
  (left.1 * right.1 - left.2 * right.2, left.1 * right.2 + left.2 * right.1)

def qComplexPower (point : QComplex) : ℕ → QComplex
  | 0 => (1, 0)
  | index + 1 => qComplexMul point (qComplexPower point index)

theorem qComplexMul_value (left right : QComplex) :
    qComplexValue (qComplexMul left right) = qComplexValue left * qComplexValue right := by
  apply Complex.ext <;> simp [qComplexValue, qComplexMul, Complex.mul_re, Complex.mul_im]

theorem qComplexPower_value (point : QComplex) (index : ℕ) :
    qComplexValue (qComplexPower point index) = qComplexValue point ^ index := by
  induction index with
  | zero => simp [qComplexPower, qComplexValue, Complex.ext_iff]
  | succ index ih => simp [qComplexPower, qComplexMul_value, ih, pow_succ']

def phaseRotation (value : ℚ) : QComplex :=
  ((4 - value * value) / (4 + value * value), (4 * value) / (4 + value * value))

theorem phaseRotation_norm (value : ℚ) : ‖qComplexValue (phaseRotation value)‖ = 1 := by
  have hd : (0 : ℝ) < 4 + (value : ℝ) * value := by nlinarith [sq_nonneg (value : ℝ)]
  have hs : ‖qComplexValue (phaseRotation value)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]
    simp only [qComplexValue, phaseRotation, Complex.normSq_apply, Rat.cast_div,
      Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    field_simp
    nlinarith [sq_nonneg (value : ℝ)]
  nlinarith [norm_nonneg (qComplexValue (phaseRotation value))]

theorem phaseRotation_linear_bound (value : ℚ) :
    ‖qComplexValue (phaseRotation value) - (1 + Complex.I * (value : ℂ))‖ ≤
      (value : ℝ) ^ 2 / 2 := by
  let delta := qComplexValue (phaseRotation value) - (1 + Complex.I * (value : ℂ))
  have hd : (0 : ℝ) < 4 + (value : ℝ) * value := by nlinarith [sq_nonneg (value : ℝ)]
  have hs : ‖delta‖ ^ 2 * (4 + (value : ℝ) * value) = (value : ℝ) ^ 4 := by
    rw [Complex.sq_norm]
    simp only [delta, qComplexValue, phaseRotation, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    field_simp
    ring
  have hprod : 0 ≤ ‖delta‖ ^ 2 * (value : ℝ) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  change ‖delta‖ ≤ _
  nlinarith [norm_nonneg delta, sq_nonneg (value : ℝ)]

theorem phaseRotation_exp_bound (value : ℚ) (hsmall : |(value : ℝ)| ≤ 1) :
    ‖qComplexValue (phaseRotation value) - Complex.exp (Complex.I * (value : ℂ))‖ ≤
      2 * (value : ℝ) ^ 2 := by
  have hz : ‖Complex.I * (value : ℂ)‖ ≤ 1 := by simpa using hsmall
  have he := Complex.norm_exp_sub_one_sub_id_le hz
  have hl := phaseRotation_linear_bound value
  have ht := norm_sub_le (qComplexValue (phaseRotation value) - (1 + Complex.I * (value : ℂ)))
    (Complex.exp (Complex.I * (value : ℂ)) - (1 + Complex.I * (value : ℂ)))
  have hidentity : (qComplexValue (phaseRotation value) - (1 + Complex.I * (value : ℂ))) -
      (Complex.exp (Complex.I * (value : ℂ)) - (1 + Complex.I * (value : ℂ))) =
      qComplexValue (phaseRotation value) - Complex.exp (Complex.I * (value : ℂ)) := by ring
  rw [hidentity] at ht
  have he' : ‖Complex.exp (Complex.I * (value : ℂ)) - (1 + Complex.I * (value : ℂ))‖ ≤
      (value : ℝ) ^ 2 := by simpa [sub_add_eq_sub_sub] using he
  nlinarith [sq_nonneg (value : ℝ)]

private theorem unit_pow_difference (left right : ℂ) (index : ℕ)
    (hl : ‖left‖ ≤ 1) (hr : ‖right‖ ≤ 1) :
    ‖left ^ index - right ^ index‖ ≤ (index : ℝ) * ‖left - right‖ := by
  induction index with
  | zero => simp
  | succ index ih =>
      have heq : left ^ (index + 1) - right ^ (index + 1) =
          left * (left ^ index - right ^ index) + (left - right) * right ^ index := by ring
      rw [heq]
      calc _ ≤ ‖left‖ * ‖left ^ index - right ^ index‖ + ‖left - right‖ * ‖right‖ ^ index := by
              simpa [norm_mul, norm_pow] using norm_add_le
                (left * (left ^ index - right ^ index)) ((left - right) * right ^ index)
        _ ≤ 1 * ((index : ℝ) * ‖left - right‖) + ‖left - right‖ * 1 := by
              gcongr
              exact pow_le_one₀ (norm_nonneg right) hr
        _ = ((index + 1 : ℕ) : ℝ) * ‖left - right‖ := by push_cast; ring

def phaseGrid (value : ℚ) (steps : ℕ) : QComplex :=
  qComplexPower (phaseRotation (value / steps)) steps

theorem phaseGrid_norm (value : ℚ) (steps : ℕ) : ‖qComplexValue (phaseGrid value steps)‖ = 1 := by
  simp [phaseGrid, qComplexPower_value, norm_pow, phaseRotation_norm]

theorem phaseGrid_exp_bound (value : ℚ) (steps : ℕ) (hsteps : 0 < steps)
    (hsmall : |(value : ℝ)| ≤ steps) :
    ‖qComplexValue (phaseGrid value steps) - Complex.exp (Complex.I * (value : ℂ))‖ ≤
      2 * (value : ℝ) ^ 2 / steps := by
  have hn : (0 : ℝ) < steps := by exact_mod_cast hsteps
  have hnC : (steps : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hsteps)
  have hstep : |(((value / steps : ℚ) : ℝ))| ≤ 1 := by
    push_cast
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr hsmall
  have he := phaseRotation_exp_bound (value / steps) hstep
  have hu : ‖Complex.exp (Complex.I * ((value / steps : ℚ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.mul_re]
    norm_num
  have hp := unit_pow_difference (qComplexValue (phaseRotation (value / steps)))
    (Complex.exp (Complex.I * ((value / steps : ℚ) : ℂ))) steps
    (phaseRotation_norm _).le hu
  have hexp : Complex.exp (Complex.I * ((value / steps : ℚ) : ℂ)) ^ steps =
      Complex.exp (Complex.I * (value : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hb := mul_le_mul_of_nonneg_left he hn.le
  rw [hexp] at hp
  dsimp only [phaseGrid]
  rw [qComplexPower_value]
  have hscale : (steps : ℝ) * (2 * (((value / steps : ℚ) : ℝ)) ^ 2) =
      2 * (value : ℝ) ^ 2 / steps := by push_cast; field_simp
  rw [hscale] at hb
  exact hp.trans hb

def phaseSteps (value error : ℚ) : ℕ :=
  1 + max (precisionFuel |value| 1) (precisionFuel (2 * value * value) error)

def phaseValue (value error : ℚ) : QComplex := phaseGrid value (phaseSteps value error)

theorem phaseValue_norm (value error : ℚ) : ‖qComplexValue (phaseValue value error)‖ = 1 :=
  phaseGrid_norm _ _

theorem phaseValue_exp_bound (value error : ℚ) (herror : 0 < error) :
    ‖qComplexValue (phaseValue value error) - Complex.exp (Complex.I * (value : ℂ))‖ ≤ (error : ℝ) := by
  have hsteps : 0 < phaseSteps value error := by simp [phaseSteps]
  have hleft : (precisionFuel |value| 1 : ℚ) ≤ phaseSteps value error := by
    exact_mod_cast (le_max_left (precisionFuel |value| 1) _).trans (Nat.le_add_left _ 1)
  have hright : (precisionFuel (2 * value * value) error : ℚ) ≤ phaseSteps value error := by
    exact_mod_cast (le_max_right _ (precisionFuel (2 * value * value) error)).trans (Nat.le_add_left _ 1)
  have hsmall : |value| ≤ (phaseSteps value error : ℚ) := by
    have h := precisionFuel_covers |value| 1 (abs_nonneg _) (by norm_num)
    simpa using h.trans (by simpa using hleft)
  have hbudget : 2 * value * value ≤ (phaseSteps value error : ℚ) * error :=
    (precisionFuel_covers (2 * value * value) error (by nlinarith [sq_nonneg value]) herror).trans
      (mul_le_mul_of_nonneg_right hright herror.le)
  have h := phaseGrid_exp_bound value (phaseSteps value error) hsteps (by exact_mod_cast hsmall)
  apply h.trans
  apply (div_le_iff₀ (by exact_mod_cast hsteps : (0 : ℝ) < phaseSteps value error)).mpr
  have hb : 2 * (value : ℝ) * value ≤ (phaseSteps value error : ℝ) * error := by
    exact_mod_cast hbudget
  nlinarith

end LandauWindows.CertificateGeometry
