import LandauWindows.Soft.MellinTail

open MeasureTheory Set

namespace LandauWindows.CertificateGeometry

def mellinIntegralCutoff (sigma : ℚ) (index : ℕ) (error : ℚ) : ℚ :=
  mellinTailCutoff (sigma - 2) index 4 error

def mellinIntegral (sigma height : ℚ) (index : ℕ) (error : ℚ) : QComplex :=
  mellinBoundedIntegral (mellinIntegralCutoff sigma index error) sigma height index (error / 2)

def mellinIntegralCheck (sigma height : ℚ) (index : ℕ) (error : ℚ) : Bool :=
  let cutoff := mellinIntegralCutoff sigma index error
  decide (0 < cutoff ∧ mellinTailRadius (sigma - 2) index 4 cutoff ≤ error / 2) &&
    mellinBoundedIntegralCheck cutoff sigma height index (error / 2)

noncomputable def mellinIntegralValue (sigma height : ℚ) (index : ℕ) : ℂ :=
  ∫ value in Ioi (0 : ℝ), realMellinIntegrand value sigma height index 1

theorem realMellinIntegrand_integrableOn (sigma height : ℚ) (index : ℕ) (hsigma : 2 < sigma) :
    IntegrableOn (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Ioi (0 : ℝ)) := by
  have hc : ContinuousOn (fun value : ℝ => realMellinIntegrand value sigma height index 1) (Icc (0 : ℝ) 1) := by
    simpa using realMellinIntegrand_continuousOn 1 sigma height index (by decide) (by linarith)
  have hf : IntervalIntegrable (fun value : ℝ => realMellinIntegrand value sigma height index 1) volume 0 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have ht := (realMellinIntegrand_tail_bound 1 sigma height index (by norm_num) hsigma).1
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact IntegrableOn.union ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hf) ht

/-- Full improper-transform accuracy for the computed cutoff and quadrature.
ACL2 proves the Boolean constructor check for every rational sigma>2,
height and positive error. All analytic growth and tail estimates used
here are proved, with no pole/coefficient conclusion among the premises. -/
theorem mellinIntegral_sound (sigma height error : ℚ) (index : ℕ)
    (hsigma : 2 < sigma) (herror : 0 < error) (hcheck : mellinIntegralCheck sigma height index error = true) :
    ‖mellinIntegralValue sigma height index - qComplexValue (mellinIntegral sigma height index error)‖ ≤ (error : ℝ) := by
  let cutoff := mellinIntegralCutoff sigma index error
  have hparams := mellinTailCutoff_adequate (sigma - 2) 4 error index (by linarith) (by decide) herror
  have hcutoff : (0 : ℚ) < cutoff := hparams.1
  have hcutoffR : (0 : ℝ) < cutoff := by exact_mod_cast hcutoff
  have htail := realMellinIntegrand_tail_bound (cutoff : ℝ) sigma height index hcutoffR hsigma
  have hf : IntervalIntegrable (fun value : ℝ => realMellinIntegrand value sigma height index 1) volume 0 (cutoff : ℝ) :=
    (realMellinIntegrand_continuousOn cutoff sigma height index hcutoff.le (by linarith)).intervalIntegrable_of_Icc hcutoffR.le
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hf htail.1
  simp only [mellinIntegralCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hbounded := mellinBoundedIntegral_sound cutoff sigma height (error / 2) index
    hcutoff.le (by linarith) (by positivity) hcheck.2
  have htailBudget : (mellinTailCoefficient (sigma - 2) index 4 : ℝ) / (cutoff : ℝ) ≤ (error : ℝ) / 2 := by
    exact_mod_cast hparams.2
  change ‖(∫ value in Ioi (0 : ℝ), realMellinIntegrand value sigma height index 1) -
    qComplexValue (mellinBoundedIntegral cutoff sigma height index (error / 2))‖ ≤ _
  rw [← hsplit]
  have heq : ∀ a b c : ℂ, (a + b) - c = (a - c) + b := by intros; ring
  rw [heq]
  calc _ ≤ ‖(∫ value in (0 : ℝ)..(cutoff : ℝ), realMellinIntegrand value sigma height index 1) -
          qComplexValue (mellinBoundedIntegral cutoff sigma height index (error / 2))‖ +
          ‖∫ value in Ioi (cutoff : ℝ), realMellinIntegrand value sigma height index 1‖ := norm_add_le _ _
    _ ≤ (error : ℝ) / 2 + (error : ℝ) / 2 := by
        apply add_le_add
        · simpa only [Rat.cast_div, Rat.cast_ofNat] using hbounded
        · exact htail.2.trans htailBudget
    _ = _ := by ring

/-- Semantic Cauchy bound when the requested precision changes the cutoff
as well as the mesh. The purely arithmetic cross-cutoff coefficient/window
comparison remains a separate part of the full Landau reduction. -/
theorem mellinIntegral_cauchy (sigma height leftError rightError : ℚ) (index : ℕ)
    (hsigma : 2 < sigma) (hleft : 0 < leftError) (hright : 0 < rightError)
    (hlcheck : mellinIntegralCheck sigma height index leftError = true)
    (hrcheck : mellinIntegralCheck sigma height index rightError = true) :
    ‖qComplexValue (mellinIntegral sigma height index leftError) -
        qComplexValue (mellinIntegral sigma height index rightError)‖ ≤ (leftError : ℝ) + rightError := by
  have hl := mellinIntegral_sound sigma height leftError index hsigma hleft hlcheck
  have hr := mellinIntegral_sound sigma height rightError index hsigma hright hrcheck
  have heq : ∀ a b c : ℂ, a - c = (a - b) + (b - c) := by intros; ring
  rw [heq _ (mellinIntegralValue sigma height index)]
  calc _ ≤ ‖qComplexValue (mellinIntegral sigma height index leftError) - mellinIntegralValue sigma height index‖ +
          ‖mellinIntegralValue sigma height index - qComplexValue (mellinIntegral sigma height index rightError)‖ :=
        norm_add_le _ _
    _ ≤ (leftError : ℝ) + rightError := add_le_add (by simpa only [norm_sub_rev] using hl) hr

end LandauWindows.CertificateGeometry
