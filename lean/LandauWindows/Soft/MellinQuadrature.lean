import LandauWindows.Soft.MellinIntegrand

namespace LandauWindows.CertificateGeometry

def qComplexAdd (left right : QComplex) : QComplex := (left.1 + right.1, left.2 + right.2)

theorem qComplexAdd_value (left right : QComplex) :
    qComplexValue (qComplexAdd left right) = qComplexValue left + qComplexValue right := by
  apply Complex.ext <;> simp [qComplexValue, qComplexAdd]

def mellinSumRaw (cells : List (ℚ × ℚ)) (sigma height : ℚ) (index : ℕ) (pointError : ℚ) : QComplex :=
  match cells with
  | [] => (0, 0)
  | cell :: rest => qComplexAdd (mellinSample cell.1 sigma height index cell.2 pointError)
      (mellinSumRaw rest sigma height index pointError)

def mellinSumError (cells : List (ℚ × ℚ)) (error : ℚ) : ℚ := error / (1 + cells.length)

def mellinSum (cells : List (ℚ × ℚ)) (sigma height : ℚ) (index : ℕ) (error : ℚ) : QComplex :=
  mellinSumRaw cells sigma height index (mellinSumError cells error)

def mellinSumCheck (cells : List (ℚ × ℚ)) (sigma : ℚ) (index : ℕ) (pointError : ℚ) : Bool :=
  cells.all (fun cell => mellinSampleCheck cell.1 sigma index cell.2 pointError)

noncomputable def mellinExactSum (cells : List (ℚ × ℚ)) (sigma height : ℚ) (index : ℕ) : ℂ :=
  match cells with
  | [] => 0
  | cell :: rest => mellinWeightedValue cell.1 sigma height index cell.2 + mellinExactSum rest sigma height index

theorem mellinSumRaw_sound (cells : List (ℚ × ℚ)) (sigma height : ℚ) (index : ℕ) (pointError : ℚ)
    (hsigma : 0 ≤ sigma) (hcells : ∀ cell ∈ cells, 0 ≤ cell.1 ∧ 0 ≤ cell.2)
    (hcheck : mellinSumCheck cells sigma index pointError = true) :
    ‖mellinExactSum cells sigma height index - qComplexValue (mellinSumRaw cells sigma height index pointError)‖ ≤
      (cells.length : ℝ) * (pointError : ℝ) := by
  induction cells with
  | nil => simp [mellinExactSum, mellinSumRaw, qComplexValue, Complex.ext_iff]
  | cons cell rest ih =>
      simp only [mellinSumCheck, List.all_cons, Bool.and_eq_true] at hcheck
      have hcell := hcells cell (by simp)
      have htail : ∀ item ∈ rest, 0 ≤ item.1 ∧ 0 ≤ item.2 :=
        fun item hi => hcells item (by simp [hi])
      have hhead := mellinSample_sound cell.1 sigma height index cell.2 pointError
        hcell.1 hsigma hcell.2 hcheck.1
      have ht := ih htail hcheck.2
      simp only [mellinExactSum, mellinSumRaw, qComplexAdd_value, List.length_cons]
      have heq : mellinWeightedValue cell.1 sigma height index cell.2 + mellinExactSum rest sigma height index -
          (qComplexValue (mellinSample cell.1 sigma height index cell.2 pointError) +
            qComplexValue (mellinSumRaw rest sigma height index pointError)) =
          (mellinWeightedValue cell.1 sigma height index cell.2 -
            qComplexValue (mellinSample cell.1 sigma height index cell.2 pointError)) +
          (mellinExactSum rest sigma height index - qComplexValue (mellinSumRaw rest sigma height index pointError)) := by ring
      rw [heq]
      calc _ ≤ ‖mellinWeightedValue cell.1 sigma height index cell.2 -
            qComplexValue (mellinSample cell.1 sigma height index cell.2 pointError)‖ +
            ‖mellinExactSum rest sigma height index - qComplexValue (mellinSumRaw rest sigma height index pointError)‖ :=
          norm_add_le _ _
        _ ≤ (pointError : ℝ) + (rest.length : ℝ) * pointError := add_le_add hhead ht
        _ = ((rest.length + 1 : ℕ) : ℝ) * pointError := by push_cast; ring

/-- Evaluation error for a fixed finite weighted grid. This does not yet
bound its discretization error against the improper Mellin integral.
ACL2 proves every constructor check as well as arithmetic Cauchy bounds. -/
theorem mellinSum_sound (cells : List (ℚ × ℚ)) (sigma height : ℚ) (index : ℕ) (error : ℚ)
    (hsigma : 0 ≤ sigma) (herror : 0 < error)
    (hcells : ∀ cell ∈ cells, 0 ≤ cell.1 ∧ 0 ≤ cell.2)
    (hcheck : mellinSumCheck cells sigma index (mellinSumError cells error) = true) :
    ‖mellinExactSum cells sigma height index - qComplexValue (mellinSum cells sigma height index error)‖ ≤
      (error : ℝ) := by
  have h := mellinSumRaw_sound cells sigma height index (mellinSumError cells error) hsigma hcells hcheck
  apply h.trans
  have he : (0 : ℝ) < error := by exact_mod_cast herror
  change (cells.length : ℝ) * (mellinSumError cells error : ℝ) ≤ (error : ℝ)
  simp only [mellinSumError, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + cells.length)).mpr
  nlinarith

end LandauWindows.CertificateGeometry
