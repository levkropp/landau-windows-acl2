import LandauWindows.Soft.SpatialBounds
import LandauWindows.Soft.KernelBounds

namespace LandauWindows.CertificateGeometry

def kernelSpatialCap (cap step : ℚ) : ℚ := step * expLipschitzCap cap

def kernelSpatialSlope (cap sigma step : ℚ) : ℚ :=
  kernelSpatialCap cap step * (1 + sigma * expLipschitzCap (sigma * cap))

theorem kernelSpatial_parameters (cap sigma step : ℚ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) :
    0 ≤ kernelSpatialCap cap step ∧ 0 ≤ kernelSpatialSlope cap sigma step := by
  have hK := (spatialBounds_parameters cap hcap).1
  have hKσ := (spatialBounds_parameters (sigma * cap) (mul_nonneg hsigma hcap)).1
  constructor <;> dsimp [kernelSpatialCap, kernelSpatialSlope] <;> positivity

noncomputable def realKernelWeight (value : ℝ) (sigma : ℚ) (index : ℕ) (step : ℚ) : ℝ :=
  (step : ℝ) * (value ^ index / index.factorial) * Real.exp (-(sigma : ℝ) * value)

private theorem taylor_term_spatial (cap : ℚ) (hcap : 0 ≤ cap) (index : ℕ) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    |left ^ index / index.factorial - right ^ index / index.factorial| ≤
      (expLipschitzCap cap : ℝ) * |left - right| := by
  have hc : Real.exp (cap : ℝ) ≤ (expLipschitzCap cap : ℝ) := (computedExpBounds_sound cap 1 hcap).2
  have hK : (0 : ℝ) ≤ expLipschitzCap cap := (Real.exp_pos (cap : ℝ)).le.trans hc
  cases index with
  | zero => simp; positivity
  | succ index =>
      have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ (index + 1) / (index + 1).factorial)
          (x ^ index / index.factorial) x := by
        convert ((hasDerivAt_id x).pow (index + 1)).div_const ((index + 1).factorial : ℝ) using 1 <;>
          first | rfl | (simp [Nat.factorial_succ]; field_simp)
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun x : ℝ => x ^ (index + 1) / (index + 1).factorial)
        (f' := fun x : ℝ => x ^ index / index.factorial) (s := Set.Icc 0 (cap : ℝ))
        (C := (expLipschitzCap cap : ℝ))
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_nonneg hx.1 _) (Nat.cast_nonneg _))]
          exact ((Real.pow_div_factorial_le_exp x hx.1 index).trans (Real.exp_le_exp.mpr hx.2)).trans hc)
        (convex_Icc _ _) hr hl
      simpa only [Real.norm_eq_abs] using h

private theorem exp_neg_spatial (cap sigma : ℚ) (hsigma : 0 ≤ sigma) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    |Real.exp (-(sigma : ℝ) * left) - Real.exp (-(sigma : ℝ) * right)| ≤
      (sigma : ℝ) * |left - right| := by
  have hs : (0 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-(sigma : ℝ) * y))
      (Real.exp (-(sigma : ℝ) * x) * (-(sigma : ℝ))) x := by
    simpa using ((hasDerivAt_id x).const_mul (-(sigma : ℝ))).exp
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => Real.exp (-(sigma : ℝ) * x))
    (f' := fun x : ℝ => Real.exp (-(sigma : ℝ) * x) * (-(sigma : ℝ)))
    (s := Set.Icc 0 (cap : ℝ)) (C := (sigma : ℝ))
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_nonneg hs]
      have he : Real.exp (-(sigma : ℝ) * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
      nlinarith)
    (convex_Icc _ _) hr hl
  simpa only [Real.norm_eq_abs] using h

theorem realKernelWeight_spatial_bound (cap sigma step : ℚ) (index : ℕ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    |realKernelWeight left sigma index step - realKernelWeight right sigma index step| ≤
      (kernelSpatialSlope cap sigma step : ℝ) * |left - right| := by
  have hc : Real.exp (cap : ℝ) ≤ (expLipschitzCap cap : ℝ) := (computedExpBounds_sound cap 1 hcap).2
  have hs : (0 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hh : (0 : ℝ) ≤ step := by exact_mod_cast hstep
  have hK : (0 : ℝ) ≤ expLipschitzCap cap := (Real.exp_pos (cap : ℝ)).le.trans hc
  have hKσ : (1 : ℝ) ≤ expLipschitzCap (sigma * cap) :=
    (Real.one_le_exp (by exact_mod_cast mul_nonneg hsigma hcap)).trans
      (computedExpBounds_sound (sigma * cap) 1 (mul_nonneg hsigma hcap)).2
  have ht := taylor_term_spatial cap hcap index hl hr
  have he := exp_neg_spatial cap sigma hsigma hl hr
  have hterm : |right ^ index / index.factorial| ≤ (expLipschitzCap cap : ℝ) := by
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hr.1 _) (Nat.cast_nonneg _))]
    exact ((Real.pow_div_factorial_le_exp right hr.1 index).trans (Real.exp_le_exp.mpr hr.2)).trans hc
  have hphase : |Real.exp (-(sigma : ℝ) * left)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hl.1])
  have hidentity : realKernelWeight left sigma index step - realKernelWeight right sigma index step =
      (step : ℝ) * ((left ^ index / index.factorial - right ^ index / index.factorial) *
        Real.exp (-(sigma : ℝ) * left) + right ^ index / index.factorial *
          (Real.exp (-(sigma : ℝ) * left) - Real.exp (-(sigma : ℝ) * right))) := by
    unfold realKernelWeight
    ring
  rw [hidentity, abs_mul, abs_of_nonneg hh]
  calc _ ≤ (step : ℝ) * (|left ^ index / index.factorial - right ^ index / index.factorial| *
          |Real.exp (-(sigma : ℝ) * left)| + |right ^ index / index.factorial| *
            |Real.exp (-(sigma : ℝ) * left) - Real.exp (-(sigma : ℝ) * right)|) := by
        gcongr
        simpa only [abs_mul] using abs_add_le
          ((left ^ index / index.factorial - right ^ index / index.factorial) * Real.exp (-(sigma : ℝ) * left))
          (right ^ index / index.factorial * (Real.exp (-(sigma : ℝ) * left) - Real.exp (-(sigma : ℝ) * right)))
    _ ≤ (step : ℝ) * ((expLipschitzCap cap : ℝ) * |left - right| * 1 +
          (expLipschitzCap cap : ℝ) * ((sigma : ℝ) * |left - right|)) := by gcongr
    _ ≤ (kernelSpatialSlope cap sigma step : ℝ) * |left - right| := by
        simp only [kernelSpatialSlope, kernelSpatialCap, Rat.cast_mul, Rat.cast_add, Rat.cast_one]
        nlinarith [mul_nonneg (mul_nonneg hh hK) (mul_nonneg hs (sub_nonneg.mpr hKσ)), abs_nonneg (left - right)]

theorem kernelWeightBounds_spatial_transport (left right cap sigma step leftError rightError : ℚ) (index : ℕ)
    (hl : 0 ≤ left) (hr : 0 ≤ right) (hlcap : left ≤ cap) (hrcap : right ≤ cap)
    (hsigma : 0 ≤ sigma) (hstep : 0 ≤ step) :
    (kernelWeightBounds left sigma index step leftError).lower -
        (kernelWeightBounds right sigma index step rightError).upper ≤
      kernelSpatialSlope cap sigma step * |left - right| := by
  have h := realKernelWeight_spatial_bound cap sigma step index (hl.trans hlcap) hsigma hstep
    (left := (left : ℝ)) (right := (right : ℝ))
    ⟨by exact_mod_cast hl, by exact_mod_cast hlcap⟩ ⟨by exact_mod_cast hr, by exact_mod_cast hrcap⟩
  have hlo := (kernelWeightBounds_sound left sigma index step leftError hl hsigma hstep).1
  have hup := (kernelWeightBounds_sound right sigma index step rightError hr hsigma hstep).2
  have hd := (le_abs_self (realKernelWeight left sigma index step - realKernelWeight right sigma index step)).trans h
  have ht : ((kernelWeightBounds left sigma index step leftError).lower : ℝ) -
      (kernelWeightBounds right sigma index step rightError).upper ≤
        (kernelSpatialSlope cap sigma step : ℝ) * |(left : ℝ) - right| := by
    dsimp [realKernelWeight] at hd
    ring_nf at hd hlo hup
    linarith
  exact_mod_cast ht

end LandauWindows.CertificateGeometry
