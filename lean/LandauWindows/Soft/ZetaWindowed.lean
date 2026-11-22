/-
THE ζ-FACING WINDOWED LANDAU THEOREM (soft layer) — ours, not lifted.

`Deduction.landau_window` (lifted, `landauWindow.lean`) is the abstract
windowed Landau theorem: from `PoleData g Φ Z` (the Mellin-transform
certificate) and `WindowHypU g θ δ` (recurring windows with a ceiling)
it concludes that every pole in `Z` has real part ≤ θ.

This file instantiates it for the Riemann zeta function:
  * `windowHypU_of_ceiling` — the elementary bridge: a ceiling
    `Gz x ≤ C x^θ` on recurring windows `[Y, Y^(3/2)]` produces
    `WindowHypU gz θ (1/2)` for the log-variable statistic `gz`;
  * `ZetaPoleData` — the analytic content (Mellin identity, pole
    structure, crude growth), injected as ONE named hypothesis, in the
    hypothesis-injection discipline (never an axiom).  Discharging it
    from mathlib's zeta machinery is the next Phase-2 milestone;
  * `zeta_landau_windowed` — Rubinstein's windowed Landau lemma for ζ,
    ceiling direction: ceilings on recurring windows `[Y, Y^(3/2)]`
    exclude zeros with real part > θ.

Corresponding classical material: ../classical/paper.tex §6 (the
effective version, which subsumes this soft statement) and
../docs/statement.md §2–3.
-/
import LandauWindows.Soft.PoleData
import LandauWindows.Soft.landauWindow
import LandauWindows.Soft.WindowHypOfRpow
import LandauWindows.Statement

open Complex MeasureTheory Set Filter Topology Formalism Deduction

noncomputable section

namespace LandauWindows

/-! ### The log-variable statistic and the zero set -/

/-- The statistic in the logarithmic variable: `gz u = Gz (e ^ u)`.
This is the paper's `g`. -/
def gz (u : ℝ) : ℝ := Gz (Real.exp u)

/-- The nontrivial zeros of ζ (the paper's zero set). -/
def zetaStripZeros : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The analytic content of the ζ-facing Landau step, as a single named
hypothesis (soft layer): SOME Φ carrying the `PoleData` structure for
`gz` over `zetaStripZeros`.  Its fields unpack to:
  meas   — measurability of `gz` (elementary; Λ-sums are step functions);
  growth — the crude bound `|Gz x| ≤ K x ^ 2` (paper, Lemma 2.1);
  laplace — the Mellin identity: `Φ s = ∫ gz e^{-s u}` for `2 < re s`
            (paper, Proposition 2.2 — the heart);
  pos    — zeros lie in the strip `0 < re < 1` (classical);
  diff   — `Φ` is holomorphic right of the axis off the zeros
            (paper, Proposition 2.2);
  iso    — the zero set has no accumulation points;
  pole   — simple poles at the zeros with residues `-ν / (ρ (ρ - 1))`
           (paper, Proposition 2.2 (2)).
The existential form is what constructions produce (`PoleData` fixes no
particular Φ; the dslope-based Φ of the construction agrees with the
naive integral on `2 < re s` by the `laplace` field).  **DISCHARGED**
(see `Soft/ZetaPoleData.lean`, ours): the lifted construction
`Deduction.poleData` at the trivial family provides it
unconditionally.  It is never an axiom. -/
def ZetaPoleData : Prop := ∃ Φ : ℂ → ℂ, PoleData gz Φ zetaStripZeros

/-! ### The ceiling-to-window bridge (elementary) -/

/-- A ceiling `g u ≤ C e ^ (θ u)` on recurring windows
`[U, (1 + δ) U]` (uniform constant `C`, arbitrarily large `U`) gives
`WindowHypU g θ δ`: take the envelope `R u = C e ^ (θ u)`, whose
θ-damped window integral is `C δ U`, eventually below `e ^ (η U`.  The
eventual comparison is the lifted `windowHyp_of_rpow_eventually`
(read with `Y = e ^ U`). -/
theorem windowHypU_of_ceiling {g : ℝ → ℝ} {θ δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 < C)
    (h : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u)) :
    WindowHypU g θ δ := by
  intro η hη U₀
  obtain ⟨Y₁, hY₁⟩ := windowHyp_of_rpow_eventually (C * δ) η (by positivity) hη
  obtain ⟨U, hU₀', hUceil⟩ := h (max U₀ (max 0 (Real.log (max 1 Y₁))))
  have hUge₀ : 0 ≤ U :=
    (le_max_left 0 _).trans ((le_max_right _ _).trans hU₀')
  have hlogU : Real.log (max 1 Y₁) ≤ U :=
    (le_max_right 0 _).trans ((le_max_right _ _).trans hU₀')
  set Y : ℝ := Real.exp U with hYdef
  have hYpos : 0 < Y := Real.exp_pos U
  have hYY₁ : Y₁ ≤ Y := by
    refine le_trans (le_max_right 1 Y₁) ?_
    calc max 1 Y₁ = Real.exp (Real.log (max 1 Y₁)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp U := Real.exp_le_exp.2 hlogU
      _ = Y := hYdef.symm
  obtain ⟨-, hK⟩ := hY₁ Y hYY₁
  have hlogY : Real.log Y = U := Real.log_exp U
  have hrpowY : Y ^ η = Real.exp (η * U) := by
    rw [Real.rpow_def_of_pos hYpos, hlogY, mul_comm]
  have hle : U ≤ (1 + δ) * U := by nlinarith
  have heq : Set.EqOn
      (fun u : ℝ => C * Real.exp (θ * u) * Real.exp (-θ * u))
      (fun _ : ℝ => C) (Icc U ((1 + δ) * U)) := by
    intro u _
    show C * Real.exp (θ * u) * Real.exp (-θ * u) = C
    have h1 : Real.exp (θ * u) * Real.exp (-θ * u) = 1 := by
      have h0 : θ * u + (-θ) * u = 0 := by ring
      rw [← Real.exp_add (θ * u) ((-θ) * u), h0, Real.exp_zero]
    rw [mul_assoc, h1, mul_one]
  refine ⟨U, le_trans (le_max_left _ _) hU₀', fun u => C * Real.exp (θ * u),
    ?_, ?_, ?_⟩
  · refine (integrableOn_congr_fun heq measurableSet_Icc).2 ?_
    exact ContinuousOn.integrableOn_Icc continuousOn_const
  · intro u hu
    exact ⟨by positivity, hUceil u hu⟩
  · rw [setIntegral_congr_fun measurableSet_Icc heq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const,
      smul_eq_mul]
    have hcalc : ((1 + δ) * U - U) * C = C * δ * Real.log Y := by
      rw [hlogY]; ring
    rw [hcalc]
    calc C * δ * Real.log Y ≤ Y ^ η := hK
      _ = Real.exp (η * U) := hrpowY

/-! ### The windowed Landau theorem for ζ (soft layer) -/

/-- **Rubinstein's windowed Landau lemma for ζ** (soft layer, ceiling
direction): if there are arbitrarily large `Y` with `Gz x ≤ C x ^ θ`
throughout the window `[Y, Y ^ (3/2)]`, then ζ has no zero with real
part `> θ`.  The analytic content enters only through the named
hypothesis `ZetaPoleData` -- **discharged unconditionally in `Soft/ZetaPoleData.lean` (ours)** -- everything else is the lifted abstract
`Deduction.landau_window` plus the elementary bridges of this file. -/
theorem zeta_landau_windowed (hP : ZetaPoleData) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) {C : ℝ} (hC : 0 < C)
    (hceil : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧
      ∀ x ∈ Icc Y (Y ^ ((3 : ℝ) / 2)), Gz x ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  -- unpack the hypothesis bundle to the underlying `PoleData`
  obtain ⟨Φ, hP'⟩ := hP
  -- the ceiling, in the log variable
  have huCeil : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + (1 / 2 : ℝ)) * U), gz u ≤ C * Real.exp (θ * u) := by
    intro U₀
    obtain ⟨Y, hY₀, hY1, hYx⟩ := hceil (Real.exp U₀)
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
      exact hbx
  -- the abstract windowed Landau theorem
  have hW : WindowHypU gz θ (1 / 2 : ℝ) :=
    windowHypU_of_ceiling (g := gz) (θ := θ) (δ := 1 / 2) (C := C)
      (by norm_num) hC huCeil
  have hwind : ∀ ρ ∈ zetaStripZeros, ρ.re ≤ θ :=
    Deduction.landau_window hP' hθ hθ1 (by norm_num) hW
  -- conclude nonvanishing right of θ
  intro s hs
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have h1' : s.re < 1 := not_le.mp h1
    by_contra h0
    have h0re : 0 < s.re := lt_trans hθ hs
    have hmem : s ∈ zetaStripZeros := ⟨h0, h0re, h1'⟩
    have hle := hwind s hmem
    linarith

end LandauWindows

end
