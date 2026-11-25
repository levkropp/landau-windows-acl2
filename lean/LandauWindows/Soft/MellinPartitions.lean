import LandauWindows.Soft.MellinSpatial
import LandauWindows.Soft.MellinQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace LandauWindows.CertificateGeometry

def mellinDyadicSum (start finish : ℚ) (depth : ℕ) (sigma height : ℚ) (index : ℕ) (pointError : ℚ) : QComplex :=
  match depth with
  | 0 => qComplexScale (finish - start) (mellinSample start sigma height index 1 pointError)
  | depth + 1 =>
      let middle := (start + finish) / 2
      qComplexAdd (mellinDyadicSum start middle depth sigma height index pointError)
        (mellinDyadicSum middle finish depth sigma height index pointError)

def mellinDyadicCheck (start finish : ℚ) (depth : ℕ) (sigma : ℚ) (index : ℕ) (pointError : ℚ) : Bool :=
  match depth with
  | 0 => mellinSampleCheck start sigma index 1 pointError
  | depth + 1 =>
      let middle := (start + finish) / 2
      mellinDyadicCheck start middle depth sigma index pointError &&
        mellinDyadicCheck middle finish depth sigma index pointError

theorem realMellinIntegrand_continuousOn (cap sigma height : ℚ) (index : ℕ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) :
    ContinuousOn (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Set.Icc 0 (cap : ℝ)) := by
  have hL : (0 : ℝ) ≤ mellinSpatialSlope cap sigma height 1 := by
    exact_mod_cast (mellinSpatial_parameters cap sigma height 1 hcap hsigma (by decide)).2.2
  have hLip : LipschitzOnWith ⟨(mellinSpatialSlope cap sigma height 1 : ℝ), hL⟩
      (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Set.Icc 0 (cap : ℝ)) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro left hl right hr
    simp only [dist_eq_norm, Real.norm_eq_abs]
    change ‖realMellinIntegrand left sigma height index 1 - realMellinIntegrand right sigma height index 1‖ ≤
      (mellinSpatialSlope cap sigma height 1 : ℝ) * |left - right|
    exact realMellinIntegrand_spatial_bound cap sigma height 1 index hcap hsigma (by decide) hl hr
  exact hLip.continuousOn

private theorem rectangle_integral_error {f : ℝ → ℂ} {start finish L error : ℝ} {sample : ℂ}
    (horder : start ≤ finish) (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Set.Icc start finish))
    (hspatial : ∀ x ∈ Set.Icc start finish, ‖f x - f start‖ ≤ L * |x - start|)
    (hsample : ‖f start - sample‖ ≤ error) :
    ‖(∫ x in start..finish, f x) - (finish - start) • sample‖ ≤
      (finish - start) * (L * (finish - start) + error) := by
  have hint : IntervalIntegrable f volume start finish := hcont.intervalIntegrable_of_Icc horder
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := start) (b := finish) (f := fun x => f x - sample)
    (C := L * (finish - start) + error) (by
      intro x hx
      rw [Set.uIoc_of_le horder] at hx
      have hspace := hspatial x ⟨hx.1.le, hx.2⟩
      have hdist : |x - start| ≤ finish - start := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
        exact sub_le_sub_right hx.2 start
      calc ‖f x - sample‖ = ‖(f x - f start) + (f start - sample)‖ := by congr 1; ring
        _ ≤ ‖f x - f start‖ + ‖f start - sample‖ := norm_add_le _ _
        _ ≤ L * (finish - start) + error := add_le_add
          (hspace.trans (mul_le_mul_of_nonneg_left hdist hL)) hsample)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const] at hbound
  simpa only [abs_of_nonneg (sub_nonneg.mpr horder), mul_comm] using hbound

/-- Actual bounded-integral error for the same dyadic tree as ACL2.
The Boolean premise contains only the existing rational sample checks;
ACL2 proves it for every valid constructor input. -/
theorem mellinDyadicSum_sound (start finish cap sigma height : ℚ) (depth index : ℕ) (pointError : ℚ)
    (hstart : 0 ≤ start) (horder : start ≤ finish) (hfinish : finish ≤ cap) (hsigma : 0 ≤ sigma)
    (_herror : 0 < pointError) (hcheck : mellinDyadicCheck start finish depth sigma index pointError = true) :
    ‖(∫ value in (start : ℝ)..(finish : ℝ), realMellinIntegrand value sigma height index 1) -
        qComplexValue (mellinDyadicSum start finish depth sigma height index pointError)‖ ≤
      ((finish : ℝ) - start) * ((mellinSpatialSlope cap sigma height 1 : ℝ) *
        (((finish : ℝ) - start) / (2 : ℝ) ^ depth) + (pointError : ℝ)) := by
  have hcap : 0 ≤ cap := hstart.trans (horder.trans hfinish)
  have hcont := realMellinIntegrand_continuousOn cap sigma height index hcap hsigma
  have hL : (0 : ℝ) ≤ mellinSpatialSlope cap sigma height 1 := by
    exact_mod_cast (mellinSpatial_parameters cap sigma height 1 hcap hsigma (by decide)).2.2
  induction depth generalizing start finish with
  | zero =>
      have hl : (start : ℝ) ∈ Set.Icc 0 (cap : ℝ) :=
        ⟨by exact_mod_cast hstart, by exact_mod_cast horder.trans hfinish⟩
      have hf : ContinuousOn (fun value => realMellinIntegrand value sigma height index 1)
          (Set.Icc (start : ℝ) (finish : ℝ)) := hcont.mono (by
        intro x hx
        constructor <;> linarith [hl.1, hx.1, hx.2, (show (finish : ℝ) ≤ cap by exact_mod_cast hfinish)])
      have hs := mellinSample_sound start sigma height index 1 pointError hstart hsigma (by decide) hcheck
      rw [← realMellinIntegrand_rat] at hs
      have hr := rectangle_integral_error (by exact_mod_cast horder) hL hf
        (fun x hx => realMellinIntegrand_spatial_bound cap sigma height 1 index hcap hsigma (by decide)
          ⟨by linarith [hl.1, hx.1], by linarith [hx.2, (show (finish : ℝ) ≤ cap by exact_mod_cast hfinish)]⟩ hl) hs
      simpa only [mellinDyadicSum, qComplexScale_value, Rat.cast_sub, Complex.ofReal_sub,
        pow_zero, div_one, Complex.real_smul, Complex.ofReal_ratCast] using hr
  | succ depth ih =>
      let middle : ℚ := (start + finish) / 2
      have hleft : start ≤ middle := by dsimp [middle]; linarith
      have hright : middle ≤ finish := by dsimp [middle]; linarith
      have hm : (middle : ℝ) = ((start : ℝ) + finish) / 2 := by simp [middle]
      simp only [mellinDyadicCheck, Bool.and_eq_true] at hcheck
      have hl := ih start middle hstart hleft (hright.trans hfinish) hcheck.1
      have hr := ih middle finish (hstart.trans hleft) hright hfinish hcheck.2
      have hf : ∀ a b : ℚ, start ≤ a → a ≤ b → b ≤ finish →
          IntervalIntegrable (fun value => realMellinIntegrand value sigma height index 1) volume (a : ℝ) (b : ℝ) := by
        intro a b ha hab hb
        apply ContinuousOn.intervalIntegrable_of_Icc (by exact_mod_cast hab)
        apply hcont.mono
        intro x hx
        constructor <;> linarith [hx.1, hx.2, (show (0 : ℝ) ≤ start by exact_mod_cast hstart),
          (show (start : ℝ) ≤ a by exact_mod_cast ha), (show (b : ℝ) ≤ finish by exact_mod_cast hb),
          (show (finish : ℝ) ≤ cap by exact_mod_cast hfinish)]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hf start middle le_rfl hleft hright) (hf middle finish hleft hright le_rfl)
      simp only [mellinDyadicSum, qComplexAdd_value]
      rw [← hsplit]
      have ht := norm_add_le
        ((∫ value in (start : ℝ)..(middle : ℝ), realMellinIntegrand value sigma height index 1) -
          qComplexValue (mellinDyadicSum start middle depth sigma height index pointError))
        ((∫ value in (middle : ℝ)..(finish : ℝ), realMellinIntegrand value sigma height index 1) -
          qComplexValue (mellinDyadicSum middle finish depth sigma height index pointError))
      have heq : ∀ a b c d : ℂ, (a + b) - (c + d) = (a - c) + (b - d) := by intros; ring
      rw [heq]
      apply ht.trans ((add_le_add hl hr).trans_eq _)
      rw [hm, pow_succ]
      field_simp
      ring

def mellinIntegralWidth (cap sigma height : ℚ) : ℚ := cap * mellinSpatialSlope cap sigma height 1 * cap

def mellinIntegralDepth (cap sigma height error : ℚ) : ℕ :=
  halvingDepth (mellinIntegralWidth cap sigma height) (error / 4)
    (precisionFuel (mellinIntegralWidth cap sigma height) (error / 4))

def mellinIntegralPrecision (cap error : ℚ) : ℚ :=
  error / (4 * (1 + cap * mellinSpatialErrorFactor cap 1))

def mellinBoundedIntegral (cap sigma height : ℚ) (index : ℕ) (error : ℚ) : QComplex :=
  mellinDyadicSum 0 cap (mellinIntegralDepth cap sigma height error) sigma height index (mellinIntegralPrecision cap error)

def mellinBoundedIntegralCheck (cap sigma height : ℚ) (index : ℕ) (error : ℚ) : Bool :=
  mellinDyadicCheck 0 cap (mellinIntegralDepth cap sigma height error) sigma index (mellinIntegralPrecision cap error)

theorem mellinIntegralDepth_adequate (cap sigma height error : ℚ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (herror : 0 < error) :
    cap * mellinSpatialSlope cap sigma height 1 * (cap / (2 : ℚ) ^ mellinIntegralDepth cap sigma height error) ≤ error / 4 := by
  have hL := (mellinSpatial_parameters cap sigma height 1 hcap hsigma (by decide)).2.2
  have hw : 0 ≤ mellinIntegralWidth cap sigma height := by dsimp [mellinIntegralWidth]; positivity
  have he : 0 < error / 4 := by positivity
  have hc := precisionFuel_covers (mellinIntegralWidth cap sigma height) (error / 4) hw he
  have hc' : mellinIntegralWidth cap sigma height ≤
      ((precisionFuel (mellinIntegralWidth cap sigma height) (error / 4) + 1 : ℕ) : ℚ) * (error / 4) := by
    push_cast
    linarith
  have hd := halvingDepth_adequate (mellinIntegralWidth cap sigma height) (error / 4)
    (precisionFuel (mellinIntegralWidth cap sigma height) (error / 4)) he hc'
  convert hd using 1
  dsimp [mellinIntegralWidth, mellinIntegralDepth]
  ring

private theorem mellinErrorFactor_one_le (cap : ℚ) (hcap : 0 ≤ cap) :
    1 ≤ mellinSpatialErrorFactor cap 1 := by
  have hm := (mellinSpatial_parameters cap 0 0 1 hcap (by decide) (by decide)).2.1
  have hk := (kernelSpatial_parameters cap 0 1 hcap (by decide) (by decide)).1
  dsimp [mellinSpatialErrorFactor]
  nlinarith [mul_nonneg hm hk]

theorem mellinIntegralPrecision_valid (cap error : ℚ) (hcap : 0 ≤ cap) (herror : 0 < error) :
    0 < mellinIntegralPrecision cap error ∧ cap * mellinIntegralPrecision cap error ≤ error / 4 := by
  have hA := mellinErrorFactor_one_le cap hcap
  have hden : 0 < 4 * (1 + cap * mellinSpatialErrorFactor cap 1) := by positivity
  constructor
  · exact div_pos herror hden
  · dsimp [mellinIntegralPrecision]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    have hca : cap ≤ cap * mellinSpatialErrorFactor cap 1 := by nlinarith
    nlinarith

/-- The computed ACL2 approximation represents the classical bounded
Mellin integral within its requested error. The sole check premise is the
finite conjunction of rational leaf checks, proved valid by ACL2's
`lw-mellin-bounded-integral-constructor-check`; neither a slope nor an
integral approximation is inserted as a hypothesis. -/
theorem mellinBoundedIntegral_sound (cap sigma height error : ℚ) (index : ℕ)
    (hcap : 0 ≤ cap) (hsigma : 0 ≤ sigma) (herror : 0 < error)
    (hcheck : mellinBoundedIntegralCheck cap sigma height index error = true) :
    ‖(∫ value in (0 : ℝ)..(cap : ℝ), realMellinIntegrand value sigma height index 1) -
        qComplexValue (mellinBoundedIntegral cap sigma height index error)‖ ≤ (error : ℝ) := by
  have hp := mellinIntegralPrecision_valid cap error hcap herror
  have hd := mellinIntegralDepth_adequate cap sigma height error hcap hsigma herror
  have hs := mellinDyadicSum_sound 0 cap cap sigma height (mellinIntegralDepth cap sigma height error) index
    (mellinIntegralPrecision cap error) (by decide) hcap le_rfl hsigma hp.1 hcheck
  simp only [Rat.cast_zero, sub_zero] at hs
  apply hs.trans
  have hdR : (cap : ℝ) * (mellinSpatialSlope cap sigma height 1 : ℝ) *
      ((cap : ℝ) / (2 : ℝ) ^ mellinIntegralDepth cap sigma height error) ≤ (error : ℝ) / 4 := by exact_mod_cast hd
  have hpR : (cap : ℝ) * (mellinIntegralPrecision cap error : ℝ) ≤ (error : ℝ) / 4 := by exact_mod_cast hp.2
  have he : (0 : ℝ) < error := by exact_mod_cast herror
  nlinarith

end LandauWindows.CertificateGeometry
