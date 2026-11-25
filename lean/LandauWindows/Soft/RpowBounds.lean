import LandauWindows.Soft.LogBounds

namespace LandauWindows.CertificateGeometry

theorem rpow_bracket_sound (value : ℚ) (numerator denominator : ℕ) (bounds : Bounds)
    (hvalue : 0 ≤ value) (hdegree : 0 < denominator) (hupper : 0 ≤ bounds.upper)
    (hlowerPower : bounds.lower ^ denominator ≤ value ^ numerator)
    (hupperPower : value ^ numerator ≤ bounds.upper ^ denominator) :
    bounds.Contains ((value : ℝ) ^ ((numerator : ℝ) / denominator)) := by
  have hv : (0 : ℝ) ≤ value := by exact_mod_cast hvalue
  have hn : (denominator : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdegree)
  have hpower : ((value : ℝ) ^ ((numerator : ℝ) / denominator)) ^ denominator =
      (value : ℝ) ^ numerator := by
    rw [← Real.rpow_mul_natCast hv]
    rw [div_mul_cancel₀ _ hn, Real.rpow_natCast]
  have hlo : (bounds.lower : ℝ) ^ denominator ≤
      ((value : ℝ) ^ ((numerator : ℝ) / denominator)) ^ denominator := by
    rw [hpower]
    exact_mod_cast hlowerPower
  have hup : ((value : ℝ) ^ ((numerator : ℝ) / denominator)) ^ denominator ≤
      (bounds.upper : ℝ) ^ denominator := by
    rw [hpower]
    exact_mod_cast hupperPower
  exact ⟨le_of_pow_le_pow_left₀ (Nat.ne_of_gt hdegree) (Real.rpow_nonneg hv _) hlo,
    le_of_pow_le_pow_left₀ (Nat.ne_of_gt hdegree) (by exact_mod_cast hupper) hup⟩

def rootBracket (target : ℚ) (degree : ℕ) (lower upper : ℚ) : ℕ → Bounds
  | 0 => ⟨lower, upper⟩
  | steps + 1 =>
      let middle := (lower + upper) / 2
      if middle ^ degree ≤ target then rootBracket target degree middle upper steps
      else rootBracket target degree lower middle steps

theorem rootBracket_sound (target : ℚ) (degree steps : ℕ) (lower upper : ℚ)
    (horder : lower ≤ upper) (hlower : lower ^ degree ≤ target)
    (hupper : target ≤ upper ^ degree) :
    let bounds := rootBracket target degree lower upper steps
    lower ≤ bounds.lower ∧ bounds.lower ≤ bounds.upper ∧ bounds.upper ≤ upper ∧
      bounds.lower ^ degree ≤ target ∧ target ≤ bounds.upper ^ degree := by
  induction steps generalizing lower upper with
  | zero => exact ⟨le_rfl, horder, le_rfl, hlower, hupper⟩
  | succ steps ih =>
      dsimp only [rootBracket]
      split_ifs with hmid
      · rcases ih ((lower + upper) / 2) upper (by linarith) hmid hupper with
          ⟨hl, ho, hu, hp, hq⟩
        exact ⟨by linarith, ho, hu, hp, hq⟩
      · rcases ih lower ((lower + upper) / 2) (by linarith) hlower (by linarith) with
          ⟨hl, ho, hu, hp, hq⟩
        exact ⟨hl, ho, by linarith, hp, hq⟩

def halvingDepth (width epsilon : ℚ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if width ≤ epsilon then 0 else 1 + halvingDepth width (2 * epsilon) fuel

def computedRpowBounds (value : ℚ) (numerator denominator : ℕ) (epsilon : ℚ) : Bounds :=
  rootBracket (value ^ numerator) denominator 1 value
    (halvingDepth (value - 1) epsilon (precisionFuel (value - 1) epsilon))

theorem computedRpowBounds_sound (value : ℚ) (numerator denominator : ℕ) (epsilon : ℚ)
    (hvalue : 1 ≤ value) (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator) :
    (computedRpowBounds value numerator denominator epsilon).Contains
      ((value : ℝ) ^ ((numerator : ℝ) / denominator)) := by
  have h := rootBracket_sound (value ^ numerator) denominator
    (halvingDepth (value - 1) epsilon (precisionFuel (value - 1) epsilon)) 1 value hvalue
    (by simpa using one_le_pow₀ hvalue : (1 : ℚ) ^ denominator ≤ value ^ numerator)
    (pow_le_pow_right₀ hvalue hexponent)
  apply rpow_bracket_sound value numerator denominator _ (by linarith) hdegree
  · exact (show (0 : ℚ) ≤ 1 by norm_num).trans (h.1.trans h.2.1)
  · exact h.2.2.2.1
  · exact h.2.2.2.2

end LandauWindows.CertificateGeometry
