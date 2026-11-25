import LandauWindows.Soft.SignalSearch

open Set

namespace LandauWindows.CertificateGeometry

noncomputable def realSmoothedSum (value : ℝ) (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.Icc 1 count,
    max 0 (value / index - 1) * ArithmeticFunction.vonMangoldt index

theorem realSmoothedSum_eq_Sz (value : ℝ) (count : ℕ) (hvalue : 0 ≤ value)
    (hcover : value ≤ count) : realSmoothedSum value count = Formalism.Sz value := by
  have hfloor : ⌊value⌋₊ ≤ count := Nat.floor_le_of_le hcover
  have hsubset : Finset.Icc 1 ⌊value⌋₊ ⊆ Finset.Icc 1 count :=
    fun index hi => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      (Finset.mem_Icc.mp hi).2.trans hfloor⟩
  rw [realSmoothedSum, ← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro index hi
    have hip : (0 : ℝ) < index := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    have hx : (index : ℝ) ≤ value :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hi).2).trans (Nat.floor_le hvalue)
    have hratio : (1 : ℝ) ≤ value / index := (le_div_iff₀ hip).mpr (by simpa using hx)
    rw [max_eq_right (by linarith : 0 ≤ value / index - 1)]
    exact mul_comm _ _
  · intro index hi hnot
    have hgt : ⌊value⌋₊ < index := by
      have hn : ¬(1 ≤ index ∧ index ≤ ⌊value⌋₊) := by simpa using hnot
      have := (Finset.mem_Icc.mp hi).1
      omega
    have hip : (0 : ℝ) < index := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    have hx : value < index := (Nat.floor_lt' (by omega)).mp hgt
    rw [max_eq_left (by have := (div_lt_one hip).mpr hx; linarith), zero_mul]

theorem realSmoothedSum_continuous (count : ℕ) :
    Continuous (fun value : ℝ => realSmoothedSum value count) := by
  unfold realSmoothedSum
  fun_prop

theorem Gz_continuousOn_Icc (left right : ℝ) (hleft : 0 < left) :
    ContinuousOn Formalism.Gz (Icc left right) := by
  have hsum : ContinuousOn Formalism.Sz (Icc left right) := by
    apply (realSmoothedSum_continuous ⌈right⌉₊).continuousOn.congr
    intro value hv
    exact (realSmoothedSum_eq_Sz value _ (hleft.le.trans hv.1)
      (hv.2.trans (Nat.le_ceil right))).symm
  have hlog : ContinuousOn Real.log (Icc left right) :=
    Real.continuousOn_log.mono (fun value hv => ne_of_gt (hleft.trans_le hv.1))
  exact (hsum.sub (continuousOn_id.mul hlog)).add (continuousOn_const.mul continuousOn_id)

/-- A ceiling on rational points extends to the whole closed positive
interval. Both endpoints are included, even when they are irrational. -/
theorem rational_ceiling_extends (left right ceiling exponent : ℝ)
    (hleft : 0 < left) (hlt : left < right)
    (hceiling : ∀ point : ℚ, (point : ℝ) ∈ Icc left right →
      Formalism.Gz point ≤ ceiling * (point : ℝ) ^ exponent) :
    ∀ point ∈ Icc left right, Formalism.Gz point ≤ ceiling * point ^ exponent := by
  let samples : Set ℝ := Ioo left right ∩ Set.range ((↑) : ℚ → ℝ)
  have hclosure : closure samples = Icc left right := by
    apply Subset.antisymm
    · exact closure_minimal (fun _ hx => ⟨hx.1.1.le, hx.1.2.le⟩) isClosed_Icc
    · have hd : Ioo left right ⊆ closure samples :=
        Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
      simpa only [closure_Ioo hlt.ne, closure_closure] using closure_mono hd
  have hf : ContinuousOn Formalism.Gz (closure samples) :=
    hclosure ▸ Gz_continuousOn_Icc left right hleft
  have hg : ContinuousOn (fun value : ℝ => ceiling * value ^ exponent) (closure samples) := by
    rw [hclosure]
    exact continuousOn_const.mul (continuousOn_id.rpow_const
      (fun value hv => Or.inl (ne_of_gt (hleft.trans_le hv.1))))
  intro point hp
  apply le_on_closure (s := samples) (f := Formalism.Gz)
    (g := fun value : ℝ => ceiling * value ^ exponent) ?_ hf hg (hclosure.symm ▸ hp)
  intro value hv
  obtain ⟨point, rfl⟩ := hv.2
  exact hceiling point ⟨hv.1.1.le, hv.1.2.le⟩

/-- Meaning of ACL2's uniform failed-search bound for the actual statistic.
The arithmetic proof supplies `hupper` at every rational window point. -/
theorem evaluated_window_ceiling_sound (start ceiling : ℚ) (right : ℝ)
    (numerator denominator : ℕ) (hstart : 1 < start) (hright : (start : ℝ) < right)
    (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (hupper : ∀ point : ℚ, (point : ℝ) ∈ Icc (start : ℝ) right →
      (signalBounds point ceiling numerator denominator (1 / 4)).upper ≤ 1) :
    ∀ point ∈ Icc (start : ℝ) right,
      Formalism.Gz point ≤ ((ceiling : ℝ) + 1) * point ^ ((numerator : ℝ) / denominator) := by
  have hs : (0 : ℝ) < start := by exact_mod_cast (lt_trans (by norm_num) hstart)
  apply rational_ceiling_extends _ _ _ _ hs hright
  intro point hp
  have hp' : 1 ≤ point := by
    have hs' : start ≤ point := by exact_mod_cast hp.1
    exact hstart.le.trans hs'
  exact evaluated_ceiling_sound point ceiling numerator denominator hp' hdegree hexponent
    (hupper point hp)

/-- The square test used by ACL2 suffices for the original `Y^(3/2)`
window; no rationality assumption on its upper endpoint is introduced. -/
theorem evaluated_landau_window_ceiling_sound (start ceiling : ℚ)
    (numerator denominator : ℕ) (hstart : 1 < start)
    (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (hupper : ∀ point : ℚ, start ≤ point → point * point ≤ start * start * start →
      (signalBounds point ceiling numerator denominator (1 / 4)).upper ≤ 1) :
    ∀ point ∈ Icc (start : ℝ) ((start : ℝ) ^ ((3 : ℝ) / 2)),
      Formalism.Gz point ≤ ((ceiling : ℝ) + 1) * point ^ ((numerator : ℝ) / denominator) := by
  have hs : (1 : ℝ) < start := by exact_mod_cast hstart
  have hs0 : (0 : ℝ) ≤ start := by linarith
  apply evaluated_window_ceiling_sound start ceiling _ numerator denominator hstart
    (Real.self_lt_rpow_of_one_lt hs (by norm_num)) hdegree hexponent
  intro point hp
  have hpoint : start ≤ point := by exact_mod_cast hp.1
  have hp0 : (0 : ℝ) ≤ point := hs0.trans hp.1
  have hpower : ((start : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (start : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hs0]
    norm_num
  have hsq : (point : ℝ) * point ≤ (start : ℝ) * start * start := by
    nlinarith [mul_self_le_mul_self hp0 hp.2]
  exact hupper point hpoint (by exact_mod_cast hsq)

end LandauWindows.CertificateGeometry
