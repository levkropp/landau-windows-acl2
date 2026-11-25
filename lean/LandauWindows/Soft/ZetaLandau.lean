/-
OURS (not lifted): the mirror (`s₀ = -1`, "floor") direction of the
archive's `Formalism.ZetaLandau`, and with it the full classical
one-sided Landau theorem for ζ (and its ε-relaxed variant), with every
analytic input discharged.

Why real nonvanishing matters.  The lifted windowed machinery runs on
ceilings: `Deduction.landau_window` concludes from `g u ≤ C e^{θu}` on
recurring windows.  A floor on `Gz` is a ceiling on `-Gz`, so the
mirror direction is `landau_window` applied to the NEGATED statistic.
The obstruction is the `pole` field of `PoleData`: at a REAL zero the
residue of the transform is a positive real (the multiplicity carries
the sign), and negating flips it, violating the positivity clause.  So
the negation goes through exactly when the zero set has no real
points.  For ζ this is classical — the paper, §8.1: "zeros ... (since
ζ(σ) < 0 on 0 < σ < 1) are non-real" — and it is not a technicality: a
real zero would contribute a POSITIVE growing term to `Gz` and be
invisible to a floor bound, which is exactly what the residue-sign
clause detects. `Soft/ZetaReal.lean` proves the sign lemma by continuing
the fractional-part integral identity to `Re s > 0`. We retain the name
of the formerly injected hypothesis:

  `ZetaNoRealStripZeros`

and discharge it as `zetaNoRealStripZeros`, so `Formalism.ZetaLandau`
and `Formalism.ZetaLandauEps` now hold unconditionally.

Contents:
  * `ZetaNoRealStripZeros`, `zetaNoRealStripZeros` — the input and its proof;
  * `poleData_neg` — `PoleData` passes to the negated statistic when
    the zero set has no real points;
  * `zeta_landau_windowed_floor` — the windowed mirror lemma;
  * `windowed_of_eventual` — an eventual one-sided bound holds
    throughout every sufficiently large window;
  * `zeta_landau`, `zeta_landau_eps` — the archive statements.
-/
import LandauWindows.Soft.ZetaWindowed
import LandauWindows.Soft.ZetaPoleData
import LandauWindows.Soft.ZetaReal
import LandauWindows.Statement

open Complex MeasureTheory Set Filter Topology Formalism Deduction

noncomputable section

namespace LandauWindows

/-! ### The discharged real nonvanishing input -/

/-- ζ has no real zeros in the open strip `0 < x < 1` (classically
equivalent to: ζ is strictly negative there).  This is the only
classical input the mirror direction needs beyond the lifted windowed
machinery; it is discharged below. -/
def ZetaNoRealStripZeros : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0

/-- The real nonvanishing input, proved from the fractional-part integral identity. -/
theorem zetaNoRealStripZeros : ZetaNoRealStripZeros := by
  intro x hx hx1
  exact riemannZeta_ne_zero_of_mem_Ioo hx hx1

/-- From the input: the strip zero set contains no real points. -/
lemma noRealStripZeros_of_im_ne_zero (h : ZetaNoRealStripZeros) :
    ∀ ρ ∈ zetaStripZeros, ρ.im ≠ 0 := by
  intro ρ hρ hρim
  have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact hρim
  rw [hρre] at hρ
  exact h ρ.re hρ.2.1 hρ.2.2 hρ.1

/-! ### PoleData passes to the negated statistic -/

/-- `PoleData` passes to the negated statistic and negated transform,
provided the zero set has no real points: the residue at a real zero
is a positive real, and negation would flip its sign, violating the
positivity clause of `pole`.  Away from the real axis the residue only
needs to be nonzero, and the windowed contradiction is a magnitude
argument. -/
theorem poleData_neg {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) (hNZ : ∀ ρ ∈ Z, ρ.im ≠ 0) :
    PoleData (fun u => -g u) (fun s => -Φ s) Z := by
  refine ⟨?_, ?_, ?_, hP.pos, ?_, hP.iso, ?_⟩
  · exact hP.meas.neg
  · obtain ⟨C, hC⟩ := hP.growth
    exact ⟨C, fun u hu => by simpa using hC u hu⟩
  · intro s hs
    have hint : ∫ u in Ioi (0 : ℝ), ((-g u : ℝ) : ℂ) * cexp (-s * u) = -Φ s := by
      rw [hP.laplace s hs, ← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      push_cast
      ring
    rw [hint]
  · exact hP.diff.neg
  · intro ρ hρ
    obtain ⟨c, hc, -, h, hlaurent⟩ := hP.pole ρ hρ
    refine ⟨-c, neg_ne_zero.2 hc, ?_, fun s => -h s, ?_, ?_⟩
    · intro him
      exact absurd him (hNZ ρ hρ)
    · exact AnalyticAt.neg hlaurent.1
    · filter_upwards [hlaurent.2] with s hs'
      rw [hs']
      ring

/-! ### The windowed floor (mirror) lemma -/

/-- **Rubinstein's windowed Landau lemma for ζ, floor (mirror)
direction** (soft layer): if there are arbitrarily large `Y` with
`Gz x ≥ -C x ^ θ` throughout the window `[Y, Y ^ (3/2)]`, then ζ has
no zero with real part `> θ`.  The analytic content is the `PoleData`
bundle for the negated statistic (`poleData_neg` over the discharged
`zetaPoleData`), using the discharged real nonvanishing input
`zetaNoRealStripZeros`; everything else is the lifted abstract
`Deduction.landau_window` plus the same elementary bridges as the
ceiling direction. -/
theorem zeta_landau_windowed_floor {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) {C : ℝ} (hC : 0 < C)
    (hfloor : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧
      ∀ x ∈ Icc Y (Y ^ ((3 : ℝ) / 2)), -Gz x ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨Φ, hΦ⟩ := zetaPoleData
  have hΦ' : PoleData (fun u => -gz u) (fun s => -Φ s) zetaStripZeros :=
    poleData_neg hΦ (noRealStripZeros_of_im_ne_zero zetaNoRealStripZeros)
  -- the floor, as a ceiling on the negated statistic in the log variable
  have huFloor : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + (1 / 2 : ℝ)) * U), -gz u ≤ C * Real.exp (θ * u) := by
    intro U₀
    obtain ⟨Y, hY₀, hY1, hYx⟩ := hfloor (Real.exp U₀)
    have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
    have hYrpow : Y ^ ((3 : ℝ) / 2)
        = Real.exp ((1 + (1 / 2 : ℝ)) * Real.log Y) := by
      rw [Real.rpow_def_of_pos hYpos, mul_comm]
      congr 1
      ring
    refine ⟨Real.log Y, ?_, ?_⟩
    · rw [← Real.exp_le_exp, Real.exp_log hYpos]
      exact hY₀
    · intro u hu
      have hxmem : Real.exp u ∈ Icc Y (Y ^ ((3 : ℝ) / 2)) := by
        refine ⟨?_, ?_⟩
        · calc Y = Real.exp (Real.log Y) := (Real.exp_log hYpos).symm
            _ ≤ Real.exp u := Real.exp_le_exp.2 hu.1
        · rw [hYrpow]
          exact Real.exp_le_exp.2 hu.2
      have hbx := hYx (Real.exp u) hxmem
      have hxpow : (Real.exp u) ^ θ = Real.exp (θ * u) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm]
      rw [hxpow] at hbx
      simpa [gz] using hbx
  have hW : WindowHypU (fun u => -gz u) θ (1 / 2 : ℝ) :=
    windowHypU_of_ceiling (g := fun u => -gz u) (θ := θ) (δ := 1 / 2) (C := C)
      (by norm_num) hC huFloor
  have hwind : ∀ ρ ∈ zetaStripZeros, ρ.re ≤ θ :=
    Deduction.landau_window hΦ' hθ hθ1 (by norm_num) hW
  intro s hs
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have h1' : s.re < 1 := not_le.mp h1
    by_contra h0
    have h0re : 0 < s.re := lt_trans hθ hs
    have hmem : s ∈ zetaStripZeros := ⟨h0, h0re, h1'⟩
    have hle := hwind s hmem
    linarith

/-! ### The eventual (classical) form -/

/-- An eventual one-sided bound holds throughout every sufficiently
large window; the constant is replaced by `|C| + 1 > 0` to meet the
windowed lemmas' shape. -/
theorem windowed_of_eventual {s₀ C x₀ θ : ℝ}
    (hbound : ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) :
    ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧
      ∀ x ∈ Icc Y (Y ^ ((3 : ℝ) / 2)), s₀ * Gz x ≤ (|C| + 1) * x ^ θ := by
  intro Y₀
  have hC1 : C ≤ |C| + 1 := by linarith [le_abs_self C]
  refine ⟨max (max Y₀ x₀) 1, ?_, le_max_right _ _, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · intro x hx
    have hx₀ : x₀ ≤ x :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx.1)
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx.1
    have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) θ
    exact le_trans (hbound x hx₀) (mul_le_mul_of_nonneg_right hC1 hxθ)

/-- **The full one-sided Landau theorem for ζ** (the archive's
`Formalism.ZetaLandau`): for EITHER sign `s₀ ∈ {1, -1}`, an eventual
one-sided bound `s₀ · Gz x ≤ C x ^ θ` excludes zeros with real part
`> θ`. Both the ceiling (`s₀ = 1`) and floor (`s₀ = -1`, mirror)
directions are unconditional. -/
theorem zeta_landau : ZetaLandau := by
  intro s₀ hs₀ θ hθ hθ1 ⟨C, x₀, hbound⟩ s hs
  have hw := windowed_of_eventual (s₀ := s₀) (C := C) (x₀ := x₀) (θ := θ) hbound
  have hC : 0 < |C| + 1 := by positivity
  rcases hs₀ with rfl | rfl
  · exact zeta_landau_windowed_unconditional hθ hθ1 hC (fun Y₀ => by
      obtain ⟨Y, hY₀, hY1, hYx⟩ := hw Y₀
      exact ⟨Y, hY₀, hY1, fun x hx => by simpa using hYx x hx⟩) s hs
  · exact zeta_landau_windowed_floor hθ hθ1 hC (fun Y₀ => by
      obtain ⟨Y, hY₀, hY1, hYx⟩ := hw Y₀
      exact ⟨Y, hY₀, hY1, fun x hx => by simpa using hYx x hx⟩) s hs

/-- **The ε-relaxed variant** (the archive's `Formalism.ZetaLandauEps`),
from `zeta_landau` by instantiating at `θ + ε` for a suitable `ε > 0`. -/
theorem zeta_landau_eps : ZetaLandauEps := by
  intro s₀ hs₀ θ hθ hθ1 hallε s hs
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have h1' : s.re < 1 := not_le.mp h1
    have hε : 0 < (s.re - θ) / 2 := by positivity
    have hθε : θ + (s.re - θ) / 2 < s.re := by linarith
    obtain ⟨C, x₀, hbound⟩ := hallε ((s.re - θ) / 2) hε
    exact zeta_landau s₀ hs₀ (θ + (s.re - θ) / 2) (by linarith)
      (by linarith) ⟨C, x₀, hbound⟩ s hθε

end LandauWindows

end
