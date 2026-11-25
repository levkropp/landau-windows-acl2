import LandauWindows.Soft.ExpBounds
import LandauWindows.Soft.SignalWindow

namespace LandauWindows.CertificateGeometry

theorem smoothedTerm_lipschitz (left right : ℝ) (index : ℕ) (hindex : 1 ≤ index) :
    |max 0 (left / index - 1) * ArithmeticFunction.vonMangoldt index -
      max 0 (right / index - 1) * ArithmeticFunction.vonMangoldt index| ≤ |left - right| := by
  have hn : (0 : ℝ) < index := by exact_mod_cast hindex
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt index := ArithmeticFunction.vonMangoldt_nonneg
  have hΛupper : ArithmeticFunction.vonMangoldt index ≤ (index : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn.le)
  have hm := abs_max_sub_max_le_abs (left / index - 1) (right / index - 1) 0
  have heq : (left / index - 1) - (right / index - 1) = (left - right) / index := by ring
  rw [heq, abs_div, abs_of_pos hn] at hm
  have heq' : max 0 (left / index - 1) * ArithmeticFunction.vonMangoldt index -
      max 0 (right / index - 1) * ArithmeticFunction.vonMangoldt index =
      (max (left / index - 1) 0 - max (right / index - 1) 0) * ArithmeticFunction.vonMangoldt index := by
    rw [max_comm 0, max_comm 0]
    ring
  rw [heq', abs_mul, abs_of_nonneg hΛ]
  calc _ ≤ (|left - right| / index) * (index : ℝ) := by gcongr
    _ = |left - right| := by field_simp

theorem realSmoothedSum_lipschitz (left right : ℝ) (count : ℕ) :
    |realSmoothedSum left count - realSmoothedSum right count| ≤ (count : ℝ) * |left - right| := by
  rw [realSmoothedSum, realSmoothedSum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ index ∈ Finset.Icc 1 count,
          |max 0 (left / index - 1) * ArithmeticFunction.vonMangoldt index -
            max 0 (right / index - 1) * ArithmeticFunction.vonMangoldt index| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index ∈ Finset.Icc 1 count, |left - right| := by
        apply Finset.sum_le_sum
        intro index hi
        exact smoothedTerm_lipschitz left right index (Finset.mem_Icc.mp hi).1
    _ = (count : ℝ) * |left - right| := by simp

theorem log_lipschitz_ge_one {left right : ℝ} (hl : 1 ≤ left) (hr : 1 ≤ right) :
    |Real.log left - Real.log right| ≤ |left - right| := by
  have hone : ∀ a b : ℝ, 1 ≤ a → a ≤ b → Real.log b - Real.log a ≤ b - a := by
    intro a b ha hab
    have h := (log_increment_bounds (by linarith : 0 < a) (by linarith : 0 < b)).2
    exact h.trans (div_le_self (sub_nonneg.mpr hab) ha)
  rcases le_total left right with hlr | hrl
  · have hm := Real.log_le_log (by linarith : 0 < left) hlr
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr hlr)]
    linarith [hone left right hl hlr]
  · have hm := Real.log_le_log (by linarith : 0 < right) hrl
    rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hrl)]
    exact hone right left hr hrl

theorem mul_log_lipschitz {left right cap : ℝ} (hl : 1 ≤ left) (hr : 1 ≤ right)
    (hlcap : left ≤ cap) (hrcap : right ≤ cap) :
    |left * Real.log left - right * Real.log right| ≤ 2 * cap * |left - right| := by
  have hlog := log_lipschitz_ge_one hl hr
  have hcap : 0 ≤ cap := by linarith
  have hlogcap : |Real.log left| ≤ cap := by
    rw [abs_of_nonneg (Real.log_nonneg hl)]
    exact (Real.log_le_self (by linarith)).trans hlcap
  have heq : left * Real.log left - right * Real.log right =
      (left - right) * Real.log left + right * (Real.log left - Real.log right) := by ring
  rw [heq]
  calc _ ≤ |(left - right) * Real.log left| + |right * (Real.log left - Real.log right)| := abs_add_le _ _
    _ = |left - right| * |Real.log left| + right * |Real.log left - Real.log right| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ right)]
    _ ≤ |left - right| * cap + cap * |left - right| := by gcongr
    _ = _ := by ring

theorem Gz_lipschitz {left right cap : ℝ} (count : ℕ) (hl : 1 ≤ left) (hr : 1 ≤ right)
    (hlcap : left ≤ cap) (hrcap : right ≤ cap) (hcount : cap ≤ count) :
    |Formalism.Gz left - Formalism.Gz right| ≤ ((count : ℝ) + 2 * cap + 3) * |left - right| := by
  have hs := realSmoothedSum_lipschitz left right count
  rw [realSmoothedSum_eq_Sz left count (by linarith) (hlcap.trans hcount),
    realSmoothedSum_eq_Sz right count (by linarith) (hrcap.trans hcount)] at hs
  have hm := mul_log_lipschitz hl hr hlcap hrcap
  have hc : |1 + Real.eulerMascheroniConstant| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  have heq : Formalism.Gz left - Formalism.Gz right =
      (Formalism.Sz left - Formalism.Sz right) - (left * Real.log left - right * Real.log right) +
        (1 + Real.eulerMascheroniConstant) * (left - right) := by unfold Formalism.Gz; ring
  rw [heq]
  calc _ ≤ |Formalism.Sz left - Formalism.Sz right - (left * Real.log left - right * Real.log right)| +
          |(1 + Real.eulerMascheroniConstant) * (left - right)| := abs_add_le _ _
    _ ≤ (|Formalism.Sz left - Formalism.Sz right| + |left * Real.log left - right * Real.log right|) +
          |1 + Real.eulerMascheroniConstant| * |left - right| := by
        rw [abs_mul]
        have ht : |Formalism.Sz left - Formalism.Sz right - (left * Real.log left - right * Real.log right)| ≤
            |Formalism.Sz left - Formalism.Sz right| + |left * Real.log left - right * Real.log right| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
            (Formalism.Sz left - Formalism.Sz right) (-(left * Real.log left - right * Real.log right))
        linarith
    _ ≤ ((count : ℝ) * |left - right| + 2 * cap * |left - right|) + 3 * |left - right| := by gcongr
    _ = _ := by ring

def logSignalCap (value : ℚ) : ℚ := 1 + (computedExpBounds value 1).upper

def logSignalLipschitz (value : ℚ) : ℚ :=
  (signalCount (logSignalCap value) : ℚ) + 2 * logSignalCap value + 3

def logSignalBudget (error : ℚ) : ℚ := min 1 error

def logSignalDelta (value error : ℚ) : ℚ :=
  logSignalBudget error / (4 * (1 + logSignalLipschitz value))

def logSignalPoint (value error : ℚ) : ℚ :=
  (computedExpBounds value (logSignalDelta value error)).lower + logSignalDelta value error

def logSignalMargin (value error : ℚ) : ℚ := logSignalLipschitz value * logSignalDelta value error

def logSignalBase (value error : ℚ) : Bounds :=
  signalBounds (logSignalPoint value error) 0 0 1 (logSignalBudget error / 2)

def logSignalBounds (value error : ℚ) : Bounds :=
  (logSignalBase value error).add ⟨-logSignalMargin value error, logSignalMargin value error⟩

theorem logSignal_parameters (value error : ℚ) (hvalue : 0 ≤ value) (herror : 0 < error) :
    2 ≤ logSignalCap value ∧ 0 ≤ logSignalLipschitz value ∧
      0 < logSignalBudget error ∧ logSignalBudget error ≤ 1 ∧
      0 < logSignalDelta value error ∧ logSignalDelta value error ≤ 1 := by
  have hc := computedExpBounds_sound value 1 hvalue
  have hlo : 1 ≤ (computedExpBounds value 1).lower := expSum_one_le value _ hvalue
  have hord : (computedExpBounds value 1).lower ≤ (computedExpBounds value 1).upper := by
    exact_mod_cast hc.1.trans hc.2
  have hcap : 2 ≤ logSignalCap value := by dsimp [logSignalCap]; linarith
  have hL : 0 ≤ logSignalLipschitz value := by
    have hn : (0 : ℚ) ≤ signalCount (logSignalCap value) := by positivity
    dsimp [logSignalLipschitz]
    linarith
  have hb : 0 < logSignalBudget error := lt_min (by norm_num) herror
  have hbone : logSignalBudget error ≤ 1 := min_le_left _ _
  have hd : 0 < logSignalDelta value error := div_pos hb (by positivity)
  have hd1 : logSignalDelta value error ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4 * (1 + logSignalLipschitz value))).mpr
    linarith
  exact ⟨hcap, hL, hb, hbone, hd, hd1⟩

theorem logSignalPoint_sound (value error : ℚ) (hvalue : 0 ≤ value) (herror : 0 < error) :
    1 < logSignalPoint value error ∧ logSignalPoint value error ≤ logSignalCap value ∧
      0 ≤ (logSignalPoint value error : ℝ) - Real.exp value ∧
      (logSignalPoint value error : ℝ) - Real.exp value ≤ (logSignalDelta value error : ℝ) := by
  rcases logSignal_parameters value error hvalue herror with ⟨_, _, _, _, hd, hd1⟩
  have hf := computedExpBounds_sound value (logSignalDelta value error) hvalue
  have hc := computedExpBounds_sound value 1 hvalue
  have hw := computedExpBounds_width value (logSignalDelta value error) hvalue hd
  have hlo : 1 ≤ (computedExpBounds value (logSignalDelta value error)).lower := expSum_one_le value _ hvalue
  have hp : 1 < logSignalPoint value error := by dsimp [logSignalPoint]; linarith
  have heq : (logSignalPoint value error : ℝ) =
      ((computedExpBounds value (logSignalDelta value error)).lower : ℝ) + (logSignalDelta value error : ℝ) := by
    simp [logSignalPoint]
  have hwR : ((computedExpBounds value (logSignalDelta value error)).upper : ℝ) -
      (computedExpBounds value (logSignalDelta value error)).lower ≤ (logSignalDelta value error : ℝ) := by
    exact_mod_cast hw
  have hdR : (logSignalDelta value error : ℝ) ≤ 1 := by exact_mod_cast hd1
  have hcap : (logSignalPoint value error : ℝ) ≤ (logSignalCap value : ℝ) := by
    simp only [logSignalCap, Rat.cast_add, Rat.cast_one]
    linarith [hf.1, hc.2]
  refine ⟨hp, by exact_mod_cast hcap, ?_, ?_⟩
  · linarith [hf.2]
  · linarith [hf.1]

/-- The fully computed rational interval encloses the log-variable
statistic. ACL2 separately proves its requested width, overlap and Cauchy
bounds; the rational sample lies within its computed transport budget. -/
theorem logSignalBounds_sound (value error : ℚ) (hvalue : 0 ≤ value) (herror : 0 < error) :
    (logSignalBounds value error).Contains (Formalism.Gz (Real.exp value)) := by
  rcases logSignal_parameters value error hvalue herror with ⟨hcap, hL, _, _, _, _⟩
  rcases logSignalPoint_sound value error hvalue herror with ⟨hpoint, hpointCap, hd, hd1⟩
  have hbase := signalBounds_sound (logSignalPoint value error) 0 (logSignalBudget error / 2) 0 1
    hpoint.le (by decide) (by decide)
  simp only [Rat.cast_zero, zero_mul, sub_zero] at hbase
  have hexp : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp (by exact_mod_cast hvalue)
  have hpR : (1 : ℝ) ≤ logSignalPoint value error := by exact_mod_cast hpoint.le
  have hpcapR : (logSignalPoint value error : ℝ) ≤ logSignalCap value := by exact_mod_cast hpointCap
  have hcount := signalCount_covers (logSignalCap value) (by linarith : 1 ≤ logSignalCap value)
  have hdiff := Gz_lipschitz (signalCount (logSignalCap value)) hpR hexp hpcapR
    (by linarith : Real.exp (value : ℝ) ≤ (logSignalCap value : ℝ)) hcount
  have hcoeff : ((signalCount (logSignalCap value) : ℝ) + 2 * (logSignalCap value : ℝ) + 3) =
      (logSignalLipschitz value : ℝ) := by simp [logSignalLipschitz]
  rw [hcoeff, abs_of_nonneg hd] at hdiff
  have hprod := mul_le_mul_of_nonneg_left hd1 (by exact_mod_cast hL : (0 : ℝ) ≤ logSignalLipschitz value)
  have habs : |Formalism.Gz (logSignalPoint value error) - Formalism.Gz (Real.exp value)| ≤
      (logSignalMargin value error : ℝ) := by
    simpa only [logSignalMargin, Rat.cast_mul] using hdiff.trans hprod
  rcases abs_le.mp habs with ⟨hneg, hpos⟩
  constructor <;> dsimp [logSignalBounds, logSignalBase, Bounds.add] <;>
    push_cast <;> linarith [hbase.1, hbase.2]

end LandauWindows.CertificateGeometry
