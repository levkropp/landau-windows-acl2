import LandauWindows.Soft.RpowBounds

open Finset Filter Topology

namespace LandauWindows.CertificateGeometry

def expTerm (value : ℚ) : ℕ → ℚ
  | 0 => 1
  | index + 1 => value * expTerm value index / (index + 1)

def expSum (value : ℚ) : ℕ → ℚ
  | 0 => 1
  | index + 1 => expSum value index + expTerm value (index + 1)

def expBand (value : ℚ) (index : ℕ) : Bounds :=
  ⟨expSum value index, expSum value index + 2 * expTerm value (index + 1)⟩

theorem expTerm_eq (value : ℚ) (index : ℕ) :
    expTerm value index = value ^ index / (index.factorial : ℚ) := by
  induction index with
  | zero => simp [expTerm]
  | succ index ih =>
      rw [expTerm, ih, pow_succ, Nat.factorial_succ]
      push_cast
      field_simp

theorem expSum_eq (value : ℚ) (index : ℕ) :
    expSum value index = ∑ term ∈ range (index + 1), value ^ term / (term.factorial : ℚ) := by
  induction index with
  | zero => simp [expSum]
  | succ index ih => simp only [expSum, ih, sum_range_succ, expTerm_eq]

theorem expSum_one_le (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value) : 1 ≤ expSum value index := by
  rw [expSum_eq]
  have hzero : (0 : ℕ) ∈ range (index + 1) := by simp
  have h := single_le_sum (fun term _ => by positivity :
    ∀ term ∈ range (index + 1), (0 : ℚ) ≤ value ^ term / (term.factorial : ℚ)) hzero
  simpa using h

theorem expTerm_nonneg (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value) :
    0 ≤ expTerm value index := by
  rw [expTerm_eq]
  positivity

theorem expTerm_half_step (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 1 : ℕ)) :
    expTerm value (index + 1) ≤ expTerm value index / 2 := by
  have hindex : (0 : ℚ) < (index + 1 : ℕ) := by positivity
  push_cast at hindex hratio
  rw [expTerm, div_le_iff₀ hindex]
  have hterm := expTerm_nonneg value index hvalue
  nlinarith

theorem expTerm_geometric_tail (value : ℚ) (index steps : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 1 : ℕ)) :
    expTerm value (index + steps) ≤ expTerm value index / (2 : ℚ) ^ steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hr : 2 * value ≤ (index + steps + 1 : ℕ) :=
        hratio.trans (by exact_mod_cast (show index + 1 ≤ index + steps + 1 by omega))
      calc expTerm value (index + (steps + 1)) = expTerm value ((index + steps) + 1) := by congr 1
        _ ≤ expTerm value (index + steps) / 2 := expTerm_half_step value _ hvalue hr
        _ ≤ (expTerm value index / (2 : ℚ) ^ steps) / 2 := by gcongr
        _ = expTerm value index / (2 : ℚ) ^ (steps + 1) := by rw [div_div, pow_succ]

theorem expBand_step (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 2 : ℕ)) :
    (expBand value (index + 1)).upper ≤ (expBand value index).upper := by
  have hnext := expTerm_half_step value (index + 1) hvalue (by simpa [Nat.add_assoc] using hratio)
  dsimp [expBand]
  rw [expSum]
  linarith

theorem expBand_later_sum (value : ℚ) (index later : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 2 : ℕ)) (hlater : index ≤ later) :
    expSum value later ≤ (expBand value index).upper := by
  have hupper : (expBand value later).upper ≤ (expBand value index).upper := by
    induction later, hlater using Nat.le_induction with
    | base => exact le_rfl
    | succ later hlater ih =>
        have hr : 2 * value ≤ (later + 2 : ℕ) :=
          hratio.trans (by exact_mod_cast Nat.add_le_add_right hlater 2)
        exact (expBand_step value later hvalue hr).trans ih
  have ht := expTerm_nonneg value (later + 1) hvalue
  dsimp [expBand] at hupper ⊢
  linarith

/-- ACL2 proves the rational index check for every computed `lw-exp-index`.
The same band contains the actual real exponential. -/
theorem expBand_sound (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 2 : ℕ)) :
    (expBand value index).Contains (Real.exp value) := by
  have hvalueR : (0 : ℝ) ≤ value := by exact_mod_cast hvalue
  constructor
  · have hs := Real.sum_le_exp_of_nonneg hvalueR (index + 1)
    simpa [expBand, expSum_eq] using hs
  · have ht : Tendsto (fun later => (expSum value later : ℝ)) atTop (𝓝 (Real.exp value)) := by
      have h := (NormedSpace.expSeries_div_hasSum_exp (value : ℝ)).tendsto_sum_nat
      rw [← Real.exp_eq_exp_ℝ] at h
      convert h.comp (tendsto_add_atTop_nat 1) using 1
      ext later
      simp [expSum_eq]
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop index] with later hlater
    exact_mod_cast expBand_later_sum value index later hvalue hratio hlater

def expNegBand (value : ℚ) (index : ℕ) : Bounds :=
  ⟨(expBand value index).upper⁻¹, (expBand value index).lower⁻¹⟩

theorem expNegBand_sound (value : ℚ) (index : ℕ) (hvalue : 0 ≤ value)
    (hratio : 2 * value ≤ (index + 2 : ℕ)) :
    (expNegBand value index).Contains (Real.exp (-(value : ℝ))) := by
  have h := expBand_sound value index hvalue hratio
  have hlow : (0 : ℝ) < (expBand value index).lower := by
    have hsum : (1 : ℚ) ≤ expSum value index := by
      rw [expSum_eq]
      have hzero : (0 : ℕ) ∈ range (index + 1) := by simp
      have hz := single_le_sum (fun term _ => by positivity :
        ∀ term ∈ range (index + 1), (0 : ℚ) ≤ value ^ term / (term.factorial : ℚ)) hzero
      simpa using hz
    have : (1 : ℝ) ≤ (expBand value index).lower := by exact_mod_cast hsum
    linarith
  have hpos : (0 : ℝ) < (expBand value index).upper := hlow.trans_le (h.1.trans h.2)
  rw [Real.exp_neg]
  constructor
  · simpa [expNegBand] using (inv_anti₀ (Real.exp_pos (value : ℝ)) h.2)
  · simpa [expNegBand] using (inv_anti₀ hlow h.1)

def ceilingLoop (value : ℚ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if value ≤ 0 then 0 else 1 + ceilingLoop (value - 1) fuel

theorem ceilingLoop_lower (value : ℚ) (fuel : ℕ) (hcover : value ≤ fuel) :
    value ≤ ceilingLoop value fuel := by
  induction fuel generalizing value with
  | zero => simpa [ceilingLoop] using hcover
  | succ fuel ih =>
      dsimp only [ceilingLoop]
      split_ifs with hvalue
      · simpa using hvalue
      · have hnext := ih (value - 1) (by push_cast at hcover; linarith)
        push_cast
        linarith

def ceilingRational (value : ℚ) : ℕ := ceilingLoop value (1 + precisionFuel value 1)

theorem ceilingRational_lower (value : ℚ) (hvalue : 0 ≤ value) : value ≤ ceilingRational value := by
  apply ceilingLoop_lower
  have hnumInt : 0 ≤ value.num := Rat.num_nonneg.mpr hvalue
  have habs : (value.num.natAbs : ℚ) = (value.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hnumInt]
  have hden : (1 : ℚ) ≤ value.den := by exact_mod_cast value.den_pos
  have hnum : (0 : ℚ) ≤ value.num := by exact_mod_cast hnumInt
  have hv : value ≤ (value.num.natAbs : ℚ) := by
    rw [habs]
    calc value = (value.num : ℚ) / value.den := value.num_div_den.symm
      _ ≤ value.num := div_le_self hnum hden
  simpa [precisionFuel] using hv.trans (le_add_of_nonneg_left (show (0 : ℚ) ≤ 1 by norm_num))

def expStartIndex (value : ℚ) : ℕ := 1 + ceilingRational (2 * value)

def expInitialWidth (value : ℚ) : ℚ := 2 * expTerm value (expStartIndex value + 1)

def expDepth (value epsilon : ℚ) : ℕ :=
  halvingDepth (expInitialWidth value) epsilon (precisionFuel (expInitialWidth value) epsilon)

def expIndex (value epsilon : ℚ) : ℕ := expStartIndex value + expDepth value epsilon

def computedExpBounds (value epsilon : ℚ) : Bounds := expBand value (expIndex value epsilon)

def computedExpNegBounds (value epsilon : ℚ) : Bounds := expNegBand value (expIndex value epsilon)

theorem expIndex_adequate (value epsilon : ℚ) (hvalue : 0 ≤ value) :
    2 * value ≤ (expIndex value epsilon + 2 : ℕ) := by
  have hceil := ceilingRational_lower (2 * value) (by linarith)
  dsimp [expIndex, expStartIndex]
  push_cast
  linarith

theorem computedExpBounds_sound (value epsilon : ℚ) (hvalue : 0 ≤ value) :
    (computedExpBounds value epsilon).Contains (Real.exp value) :=
  expBand_sound value _ hvalue (expIndex_adequate value epsilon hvalue)

theorem computedExpNegBounds_sound (value epsilon : ℚ) (hvalue : 0 ≤ value) :
    (computedExpNegBounds value epsilon).Contains (Real.exp (-(value : ℝ))) :=
  expNegBand_sound value _ hvalue (expIndex_adequate value epsilon hvalue)

theorem halvingDepth_adequate (width epsilon : ℚ) (fuel : ℕ) (hepsilon : 0 < epsilon)
    (hcover : width ≤ ((fuel + 1 : ℕ) : ℚ) * epsilon) :
    width / (2 : ℚ) ^ (halvingDepth width epsilon fuel) ≤ epsilon := by
  induction fuel generalizing epsilon with
  | zero => simpa [halvingDepth] using hcover
  | succ fuel ih =>
      by_cases h : width ≤ epsilon
      · simp [halvingDepth, h]
      · have hc : width ≤ ((fuel + 1 : ℕ) : ℚ) * (2 * epsilon) := by
          push_cast at hcover ⊢
          nlinarith
        have ht := ih (2 * epsilon) (by positivity) hc
        simp only [halvingDepth, h, if_false, pow_add, pow_one]
        rw [mul_comm (2 : ℚ), ← div_div]
        linarith

theorem computedExpBounds_width (value epsilon : ℚ) (hvalue : 0 ≤ value) (hepsilon : 0 < epsilon) :
    (computedExpBounds value epsilon).upper - (computedExpBounds value epsilon).lower ≤ epsilon := by
  have hw : 0 ≤ expInitialWidth value := by
    exact mul_nonneg (by norm_num) (expTerm_nonneg value _ hvalue)
  have hc : expInitialWidth value ≤ ((precisionFuel (expInitialWidth value) epsilon + 1 : ℕ) : ℚ) * epsilon := by
    have h := precisionFuel_covers (expInitialWidth value) epsilon hw hepsilon
    push_cast
    nlinarith
  have hd := halvingDepth_adequate (expInitialWidth value) epsilon
    (precisionFuel (expInitialWidth value) epsilon) hepsilon hc
  have hr : 2 * value ≤ (expStartIndex value + 1 + 1 : ℕ) := by
    have h := ceilingRational_lower (2 * value) (by linarith)
    dsimp [expStartIndex]
    push_cast
    linarith
  have ht := expTerm_geometric_tail value (expStartIndex value + 1) (expDepth value epsilon) hvalue hr
  have heq : expIndex value epsilon + 1 = expStartIndex value + 1 + expDepth value epsilon := by
    dsimp [expIndex]
    omega
  have hbound : 2 * expTerm value (expIndex value epsilon + 1) ≤ epsilon := by
    rw [heq]
    calc _ ≤ 2 * (expTerm value (expStartIndex value + 1) / (2 : ℚ) ^ (expDepth value epsilon)) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = expInitialWidth value / (2 : ℚ) ^ (expDepth value epsilon) := by rw [expInitialWidth]; ring
      _ ≤ epsilon := hd
  simpa [computedExpBounds, expBand] using hbound

end LandauWindows.CertificateGeometry
