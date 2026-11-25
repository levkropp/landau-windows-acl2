import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
OURS (not lifted): the fractional-part integral continuation of zeta to `Re s > 0`,
and its strict negativity on the real interval `(0, 1)`.

The bounded fractional-part tail has a Mellin transform analytic on the right half-plane.
Abel summation identifies it with `1 / (s - 1) - zeta(s) / s` when `Re s > 1`.
Multiplying by `s - 1` removes the pole; the identity theorem on the connected right
half-plane then gives the continuation. On the real strip the integral is nonnegative,
so `zeta(x) <= x / (x - 1) < 0`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace LandauWindows

private def fractionalPartTail : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ))

private lemma fractionalPartTail_measurable : Measurable fractionalPartTail :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

private lemma fractionalPartTail_norm_le (t : ℝ) : ‖fractionalPartTail t‖ ≤ 1 := by
  by_cases ht : 1 < t
  · simpa [fractionalPartTail, ht, abs_of_nonneg (Int.fract_nonneg t)] using
      (Int.fract_lt_one t).le
  · simp [fractionalPartTail, ht]

private lemma fractionalPartTail_locallyIntegrable :
    LocallyIntegrableOn fractionalPartTail (Ioi 0) := by
  refine ((locallyIntegrable_const (1 : ℂ)).mono
    fractionalPartTail_measurable.aestronglyMeasurable ?_).locallyIntegrableOn _
  exact Eventually.of_forall fun t => by simpa using fractionalPartTail_norm_le t

private lemma fractionalPartTail_top :
    fractionalPartTail =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
  simpa using fractionalPartTail_norm_le t

private lemma fractionalPartTail_bot (b : ℝ) :
    fractionalPartTail =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  simp [fractionalPartTail, not_lt_of_ge ht.le]

/-- The fractional-part remainder in the integral continuation of zeta. -/
def zetaFractionalPartIntegral (s : ℂ) : ℂ := mellin fractionalPartTail (-s)

lemma zetaFractionalPartIntegral_eq_integral (s : ℂ) :
    zetaFractionalPartIntegral s =
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) := by
  unfold zetaFractionalPartIntegral mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioi (1 : ℝ))
    measurableSet_Ioi (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      simp [fractionalPartTail, ht, smul_eq_mul]
  · intro t ht
    simp [fractionalPartTail, ht.2]

lemma differentiableAt_zetaFractionalPartIntegral {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFractionalPartIntegral s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    fractionalPartTail_locallyIntegrable fractionalPartTail_top
    (show (-s).re < 0 by simpa using hs)
    (fractionalPartTail_bot (-s.re - 1)) (by simp : -s.re - 1 < (-s).re)
  exact hm.comp s differentiableAt_id.neg

private lemma integrableOn_fractionalPart {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ))
      (Ioi 1) := by
  have hm := mellinConvergent_of_isBigO_rpow
    fractionalPartTail_locallyIntegrable fractionalPartTail_top
    (show (-s).re < 0 by simpa using hs)
    (fractionalPartTail_bot (-s.re - 1)) (by simp : -s.re - 1 < (-s).re)
  exact (hm.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun
    (fun t ht => by simp [fractionalPartTail, ht, smul_eq_mul]) measurableSet_Ioi

private lemma zeta_eq_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t : ℝ in Ioi 1, (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hbound : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℂ)‖)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    simpa using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  simpa [LSeries_one_eq_riemannZeta hs] using
    LSeries_eq_mul_integral' (1 : ℕ → ℂ) (by norm_num : (0 : ℝ) ≤ 1) hs hbound

private lemma zeta_eq_fractionalPart_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * zetaFractionalPartIntegral s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hpower : (-s).re < -1 := by simpa using hs
  have hfloor : (fun t : ℝ => (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =ᶠ[
      ae (volume.restrict (Ioi 1))]
      (fun t : ℝ => (t : ℂ) ^ (-s) -
        (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := le_trans zero_le_one ht.le
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one ht.le).ne'
    have hcast : (⌊t⌋₊ : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← ofReal_natCast, natCast_floor_eq_intCast_floor ht0, Int.fract]
      push_cast
      ring
    dsimp only
    rw [hcast, show -(s + 1) = -s - 1 by ring, cpow_sub _ _ htC, cpow_one]
    field_simp
  rw [zeta_eq_integral_floor hs, integral_congr_ae hfloor,
    integral_sub (integrableOn_Ioi_cpow_of_lt hpower zero_lt_one)
      (integrableOn_fractionalPart hs0), integral_Ioi_cpow_of_lt hpower zero_lt_one,
    ← zetaFractionalPartIntegral_eq_integral]
  simp only [ofReal_one, one_cpow]
  rw [show -s + 1 = -(s - 1) by ring, div_neg]
  ring

/-- The fractional-part identity continued across the pole after multiplying by `s - 1`. -/
theorem riemannZeta₁_eq_fractionalPart {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ s = s - s * (s - 1) * zetaFractionalPartIntegral s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have han : AnalyticOnNhd ℂ
      (fun s => s - s * (s - 1) * zetaFractionalPartIntegral s) {s : ℂ | 0 < s.re} := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hopen
    exact (differentiableAt_id.sub ((differentiableAt_id.mul
      (differentiableAt_id.sub_const 1)).mul
      (differentiableAt_zetaFractionalPartIntegral hs))).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 0 < s.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  refine (hz.eqOn_of_preconnected_of_eventuallyEq
    han (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2 : ℂ) ∈
      {s : ℂ | 0 < s.re}) ?_) hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)] with s hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hid := zeta_eq_fractionalPart_of_one_lt_re hs
  rw [riemannZeta_eq_inv_sub_mul hs1] at hid
  field_simp at hid
  linear_combination hid

/-- For `Re s > 0`, away from the pole, zeta has its fractional-part integral representation. -/
theorem riemannZeta_eq_fractionalPart {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * zetaFractionalPartIntegral s := by
  rw [riemannZeta_eq_inv_sub_mul hs1, riemannZeta₁_eq_fractionalPart hs]
  field_simp

lemma zetaFractionalPartIntegral_ofReal (x : ℝ) :
    zetaFractionalPartIntegral x =
      ((∫ t : ℝ in Ioi 1, t ^ (-x - 1) * Int.fract t : ℝ) : ℂ) := by
  rw [zetaFractionalPartIntegral_eq_integral, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ofReal_mul, ofReal_cpow (le_trans zero_le_one ht.le)]
  push_cast
  rfl

/-- Zeta is strictly negative on the real open critical strip. -/
theorem riemannZeta_re_neg_of_mem_Ioo {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (riemannZeta x).re < 0 := by
  have hnonneg : 0 ≤ ∫ t : ℝ in Ioi 1, t ^ (-x - 1) * Int.fract t := by
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one ht.le) _) (Int.fract_nonneg t)
  have hxC : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have hreal : riemannZeta x = ((x / (x - 1) -
      x * ∫ t : ℝ in Ioi 1, t ^ (-x - 1) * Int.fract t : ℝ) : ℂ) := by
    rw [riemannZeta_eq_fractionalPart (by simpa using hx) hxC,
      zetaFractionalPartIntegral_ofReal]
    push_cast
    rfl
  rw [hreal, ofReal_re]
  linarith [div_neg_of_pos_of_neg hx (sub_neg.mpr hx1), mul_nonneg hx.le hnonneg]

/-- Zeta has no real zero in the open critical strip. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    riemannZeta x ≠ 0 := by
  intro hzero
  exact (riemannZeta_re_neg_of_mem_Ioo hx hx1).ne (congrArg Complex.re hzero)

end LandauWindows

end
