import LandauWindows.Soft.LogSignal
import Mathlib.Analysis.Calculus.MeanValue

namespace LandauWindows.CertificateGeometry

/-- The same rational constant used by `exp-continuity.lisp`. -/
def expLipschitzCap (cap : ℚ) : ℚ := (computedExpBounds cap 1).upper

def logSignalSpatialCap (cap : ℚ) : ℚ := 2 + expLipschitzCap cap

def logSignalSpatialSlope (cap : ℚ) : ℚ :=
  (signalCount (logSignalSpatialCap cap) : ℚ) + 2 * logSignalSpatialCap cap + 3

def logSignalModulus (cap error : ℚ) : ℚ :=
  error / (4 * (1 + logSignalSpatialSlope cap * expLipschitzCap cap))

theorem spatialBounds_parameters (cap : ℚ) (hcap : 0 ≤ cap) :
    1 ≤ expLipschitzCap cap ∧ 3 ≤ logSignalSpatialCap cap ∧ 0 ≤ logSignalSpatialSlope cap := by
  have hc := (computedExpBounds_sound cap 1 hcap).2
  have he : (1 : ℝ) ≤ Real.exp (cap : ℝ) := Real.one_le_exp (by exact_mod_cast hcap)
  have hK : (1 : ℚ) ≤ expLipschitzCap cap := by
    exact_mod_cast he.trans hc
  have hB : 3 ≤ logSignalSpatialCap cap := by dsimp [logSignalSpatialCap]; linarith
  have hS : 0 ≤ logSignalSpatialSlope cap := by
    have hn : (0 : ℚ) ≤ signalCount (logSignalSpatialCap cap) := by positivity
    dsimp [logSignalSpatialSlope]
    linarith
  exact ⟨hK, hB, hS⟩

/-- The computed majorant applies on the entire real log interval. The
arithmetic proof independently derives transport from finite Taylor sums. -/
theorem exp_spatial_bound (cap : ℚ) (hcap : 0 ≤ cap) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    |Real.exp left - Real.exp right| ≤ (expLipschitzCap cap : ℝ) * |left - right| := by
  have hc := (computedExpBounds_sound cap 1 hcap).2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Set.Icc 0 (cap : ℝ))
    (C := (expLipschitzCap cap : ℝ))
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact (Real.exp_le_exp.mpr hx.2).trans hc)
    (convex_Icc _ _) hr hl
  simpa only [Real.norm_eq_abs] using h

/-- A uniform Lipschitz constant for the actual logarithmic statistic,
including integer breakpoints of the smoothed prime-power sum. -/
theorem logSignal_spatial_bound (cap : ℚ) (hcap : 0 ≤ cap) {left right : ℝ}
    (hl : left ∈ Set.Icc 0 (cap : ℝ)) (hr : right ∈ Set.Icc 0 (cap : ℝ)) :
    |Formalism.Gz (Real.exp left) - Formalism.Gz (Real.exp right)| ≤
      (logSignalSpatialSlope cap : ℝ) * (expLipschitzCap cap : ℝ) * |left - right| := by
  rcases spatialBounds_parameters cap hcap with ⟨_, hB, hS⟩
  have hc := (computedExpBounds_sound cap 1 hcap).2
  change Real.exp (cap : ℝ) ≤ (expLipschitzCap cap : ℝ) at hc
  have hBexp : Real.exp (cap : ℝ) ≤ (logSignalSpatialCap cap : ℝ) := by
    simp only [logSignalSpatialCap, Rat.cast_add, Rat.cast_ofNat]
    linarith
  have hcount := signalCount_covers (logSignalSpatialCap cap) (by linarith : 1 ≤ logSignalSpatialCap cap)
  have hG := Gz_lipschitz (signalCount (logSignalSpatialCap cap))
    (Real.one_le_exp hl.1) (Real.one_le_exp hr.1)
    ((Real.exp_le_exp.mpr hl.2).trans hBexp) ((Real.exp_le_exp.mpr hr.2).trans hBexp) hcount
  have hcoeff : ((signalCount (logSignalSpatialCap cap) : ℝ) + 2 * (logSignalSpatialCap cap : ℝ) + 3) =
      (logSignalSpatialSlope cap : ℝ) := by simp [logSignalSpatialSlope]
  rw [hcoeff] at hG
  have he := exp_spatial_bound cap hcap hl hr
  calc _ ≤ (logSignalSpatialSlope cap : ℝ) * |Real.exp left - Real.exp right| := hG
    _ ≤ (logSignalSpatialSlope cap : ℝ) * ((expLipschitzCap cap : ℝ) * |left - right|) :=
      mul_le_mul_of_nonneg_left he (by exact_mod_cast hS)
    _ = _ := by ring

/-- Semantic counterpart of ACL2's precision-free lower-to-upper transport.
All endpoints are those of the existing computed signal enclosures. -/
theorem logSignalBounds_spatial_transport (left right cap leftError rightError : ℚ)
    (hl : 0 ≤ left) (hr : 0 ≤ right) (hlcap : left ≤ cap) (hrcap : right ≤ cap)
    (hlerror : 0 < leftError) (hrerror : 0 < rightError) :
    (logSignalBounds left leftError).lower - (logSignalBounds right rightError).upper ≤
      logSignalSpatialSlope cap * expLipschitzCap cap * |left - right| := by
  have hcap : 0 ≤ cap := hl.trans hlcap
  have hs := logSignal_spatial_bound cap hcap
    (left := (left : ℝ)) (right := (right : ℝ))
    ⟨by exact_mod_cast hl, by exact_mod_cast hlcap⟩
    ⟨by exact_mod_cast hr, by exact_mod_cast hrcap⟩
  have hlo := (logSignalBounds_sound left leftError hl hlerror).1
  have hup := (logSignalBounds_sound right rightError hr hrerror).2
  have hd := (le_abs_self (Formalism.Gz (Real.exp (left : ℝ)) - Formalism.Gz (Real.exp (right : ℝ)))).trans hs
  have ht : ((logSignalBounds left leftError).lower : ℝ) - (logSignalBounds right rightError).upper ≤
      (logSignalSpatialSlope cap : ℝ) * (expLipschitzCap cap : ℝ) * |(left : ℝ) - right| := by linarith
  exact_mod_cast ht

/-- The rational mesh spacing is positive and bounds the real spatial error.
ACL2 also accounts for the two computed endpoint evaluation errors. -/
theorem logSignalModulus_sound (cap error : ℚ) (hcap : 0 ≤ cap) (herror : 0 < error) :
    0 < logSignalModulus cap error ∧
      ∀ left right : ℝ, left ∈ Set.Icc 0 (cap : ℝ) → right ∈ Set.Icc 0 (cap : ℝ) →
        |left - right| ≤ (logSignalModulus cap error : ℝ) →
        |Formalism.Gz (Real.exp left) - Formalism.Gz (Real.exp right)| ≤ (error : ℝ) / 4 := by
  rcases spatialBounds_parameters cap hcap with ⟨hK, _, hS⟩
  have hA : 0 ≤ logSignalSpatialSlope cap * expLipschitzCap cap := mul_nonneg hS (by linarith)
  have hd : (0 : ℚ) < 4 * (1 + logSignalSpatialSlope cap * expLipschitzCap cap) := by positivity
  have hmod : 0 < logSignalModulus cap error := div_pos herror hd
  refine ⟨hmod, ?_⟩
  intro left right hl hr hdist
  have hb : logSignalSpatialSlope cap * expLipschitzCap cap * logSignalModulus cap error ≤ error / 4 := by
    dsimp [logSignalModulus]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  calc _ ≤ (logSignalSpatialSlope cap : ℝ) * (expLipschitzCap cap : ℝ) * |left - right| :=
      logSignal_spatial_bound cap hcap hl hr
    _ ≤ (logSignalSpatialSlope cap : ℝ) * (expLipschitzCap cap : ℝ) * (logSignalModulus cap error : ℝ) :=
      mul_le_mul_of_nonneg_left hdist (by exact_mod_cast hA)
    _ ≤ (error : ℝ) / 4 := by exact_mod_cast hb

end LandauWindows.CertificateGeometry
