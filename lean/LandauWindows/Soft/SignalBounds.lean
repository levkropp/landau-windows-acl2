import LandauWindows.Statement
import LandauWindows.Soft.PrimePowers
import LandauWindows.Soft.EulerBounds
import LandauWindows.Soft.RpowBounds

namespace LandauWindows.CertificateGeometry

def Bounds.scale (coefficient : ℚ) (bounds : Bounds) : Bounds :=
  if 0 ≤ coefficient then ⟨coefficient * bounds.lower, coefficient * bounds.upper⟩
  else ⟨coefficient * bounds.upper, coefficient * bounds.lower⟩

theorem Bounds.scale_sound (coefficient : ℚ) {bounds : Bounds} {value : ℝ}
    (hvalue : bounds.Contains value) :
    (bounds.scale coefficient).Contains ((coefficient : ℝ) * value) := by
  rcases hvalue with ⟨hlower, hupper⟩
  by_cases hsign : 0 ≤ coefficient
  · have hc : (0 : ℝ) ≤ coefficient := by exact_mod_cast hsign
    constructor <;> simp only [scale, hsign, if_true, Rat.cast_mul]
    · exact mul_le_mul_of_nonneg_left hlower hc
    · exact mul_le_mul_of_nonneg_left hupper hc
  · have hc : (coefficient : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hsign)
    constructor <;> simp only [scale, hsign, if_false, Rat.cast_mul]
    · exact mul_le_mul_of_nonpos_left hupper hc
    · exact mul_le_mul_of_nonpos_left hlower hc

def ramp (value : ℚ) (index : ℕ) : ℚ := max 0 (value / index - 1)

def smoothedSumBounds (value epsilon : ℚ) : ℕ → Bounds
  | 0 => ⟨0, 0⟩
  | count + 1 => ((mangoldtBounds (count + 1) epsilon).scale (ramp value (count + 1))).add
      (smoothedSumBounds value epsilon count)

noncomputable def smoothedSumValue (value : ℚ) (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.Icc 1 count, (ramp value index : ℝ) * ArithmeticFunction.vonMangoldt index

theorem smoothedSumBounds_sound (value epsilon : ℚ) (count : ℕ) :
    (smoothedSumBounds value epsilon count).Contains (smoothedSumValue value count) := by
  induction count with
  | zero => simp [smoothedSumBounds, smoothedSumValue, Bounds.Contains]
  | succ count ih =>
      have hterm := Bounds.scale_sound (ramp value (count + 1)) (mangoldtBounds_sound (count + 1) epsilon)
      have hsum := Bounds.add_sound hterm ih
      simpa [smoothedSumBounds, smoothedSumValue, Finset.sum_Icc_succ_top, add_comm] using hsum

theorem smoothedSumValue_eq_Sz (value : ℚ) (count : ℕ) (hvalue : 0 ≤ value)
    (hcover : (value : ℝ) ≤ count) :
    smoothedSumValue value count = Formalism.Sz value := by
  have hfloor : ⌊(value : ℝ)⌋₊ ≤ count := Nat.floor_le_of_le hcover
  have hsubset : Finset.Icc 1 ⌊(value : ℝ)⌋₊ ⊆ Finset.Icc 1 count :=
    fun index hindex => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hindex).1,
      (Finset.mem_Icc.mp hindex).2.trans hfloor⟩
  rw [smoothedSumValue, ← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro index hindex
    have hi : 0 < (index : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hindex).1
    have hx : (index : ℝ) ≤ value := (Nat.cast_le.mpr (Finset.mem_Icc.mp hindex).2).trans
      (Nat.floor_le (by exact_mod_cast hvalue))
    have hramp : (ramp value index : ℝ) = (value : ℝ) / index - 1 := by
      simp only [ramp, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one]
      apply max_eq_right
      have hratio : (1 : ℝ) ≤ (value : ℝ) / index := (le_div_iff₀ hi).mpr (by simpa using hx)
      linarith
    simp only [hramp, mul_comm]
  · intro index hindex hnot
    have hindexLow := (Finset.mem_Icc.mp hindex).1
    have hindexGt : ⌊(value : ℝ)⌋₊ < index := by
      have hnot' : ¬(1 ≤ index ∧ index ≤ ⌊(value : ℝ)⌋₊) := by simpa using hnot
      omega
    have hx : (value : ℝ) < index := (Nat.floor_lt' (by omega)).mp hindexGt
    have hi : 0 < (index : ℝ) := by exact_mod_cast hindexLow
    have hramp : (ramp value index : ℝ) = 0 := by
      simp only [ramp, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one]
      exact max_eq_left (by have := (div_lt_one hi).mpr hx; linarith)
    simp only [hramp, zero_mul]

def gzBoundsRaw (value : ℚ) (count : ℕ) (epsilon : ℚ) : Bounds :=
  ((smoothedSumBounds value epsilon count).sub ((computedLogBounds value epsilon).scale value)).add
    (((Bounds.point 1).add (computedEulerBounds epsilon)).scale value)

theorem gzBoundsRaw_sound (value epsilon : ℚ) (count : ℕ)
    (hvalue : 1 ≤ value) (hcover : (value : ℝ) ≤ count) :
    (gzBoundsRaw value count epsilon).Contains (Formalism.Gz value) := by
  have hsum := smoothedSumBounds_sound value epsilon count
  rw [smoothedSumValue_eq_Sz value count (by linarith) hcover] at hsum
  have hlog := Bounds.scale_sound value (computedLogBounds_sound value epsilon hvalue)
  have heuler := Bounds.scale_sound value (Bounds.add_sound (Bounds.point_sound 1)
    (computedEulerBounds_sound epsilon))
  have h := Bounds.add_sound (Bounds.sub_sound hsum hlog) heuler
  simpa only [gzBoundsRaw, Formalism.Gz, Rat.cast_one, mul_comm] using h

def signalCount (value : ℚ) : ℕ := value.num.natAbs

theorem signalCount_covers (value : ℚ) (hvalue : 1 ≤ value) :
    (value : ℝ) ≤ signalCount value := by
  have hnonneg : 0 ≤ value := by linarith
  have hden : (1 : ℝ) ≤ value.den := by exact_mod_cast value.den_pos
  have hnum : (0 : ℝ) ≤ value.num := by exact_mod_cast (Rat.num_nonneg.mpr hnonneg)
  have habs : (value.num.natAbs : ℝ) = (value.num : ℝ) := by
    have hnumInt : 0 ≤ value.num := Rat.num_nonneg.mpr hnonneg
    rw [Nat.cast_natAbs, abs_of_nonneg hnumInt]
  rw [signalCount, habs]
  rw [Rat.cast_def]
  exact div_le_self hnum hden

def signalErrorFactor (value ceiling : ℚ) : ℚ := ((signalCount value : ℚ) + 2) * value + ceiling

def signalPrecision (value ceiling error : ℚ) : ℚ := error / (1 + signalErrorFactor value ceiling)

def signalBoundsRaw (value : ℚ) (count : ℕ) (ceiling : ℚ)
    (numerator denominator : ℕ) (epsilon : ℚ) : Bounds :=
  (gzBoundsRaw value count epsilon).sub
    ((computedRpowBounds value numerator denominator epsilon).scale ceiling)

def signalBounds (value ceiling : ℚ) (numerator denominator : ℕ) (error : ℚ) : Bounds :=
  signalBoundsRaw value (signalCount value) ceiling numerator denominator
    (signalPrecision value ceiling error)

theorem signalBounds_sound (value ceiling error : ℚ) (numerator denominator : ℕ)
    (hvalue : 1 ≤ value) (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator) :
    (signalBounds value ceiling numerator denominator error).Contains
      (Formalism.Gz value - (ceiling : ℝ) * (value : ℝ) ^ ((numerator : ℝ) / denominator)) := by
  apply Bounds.sub_sound
  · exact gzBoundsRaw_sound value _ _ hvalue (signalCount_covers value hvalue)
  · exact Bounds.scale_sound ceiling (computedRpowBounds_sound value numerator denominator _
      hvalue hdegree hexponent)

theorem signalBounds_violation (value ceiling error : ℚ) (numerator denominator : ℕ)
    (hvalue : 1 ≤ value) (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (hpositive : 0 < (signalBounds value ceiling numerator denominator error).lower) :
    (ceiling : ℝ) * (value : ℝ) ^ ((numerator : ℝ) / denominator) < Formalism.Gz value := by
  have h := (signalBounds_sound value ceiling error numerator denominator hvalue hdegree hexponent).1
  have hp : (0 : ℝ) < (signalBounds value ceiling numerator denominator error).lower := by
    exact_mod_cast hpositive
  linarith

end LandauWindows.CertificateGeometry
