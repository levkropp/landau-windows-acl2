/-
OURS (not lifted): the zeta instantiation of the lifted PoleData
construction — the discharge of the soft layer's analytic hypothesis.

The lifted construction (PoleDataConstruction.lean) is unconditional for
every admissible character family:
    Deduction.poleData F : ∃ Φ, PoleData (gm F) Φ (zeroSet F).
Instantiating at the trivial family (the conductor-1 character alone,
weight 1) gives the zeta case, because
  * the family statistic `gm Ftriv` IS our `gz`: the trivial-character
    branch of the archive's `Gchi` is `Gz` by construction, and
    `ramp (fun _ => 1) y = Sz y` is the bridge to `Formalism.Sz`;
  * the family zero set `zeroSet Ftriv` IS our `zetaStripZeros`: the
    conductor-1 L-function is `riemannZeta`, and the conjugate
    disjunct collapses since zeta (conj rho) = conj (zeta rho), with
    the `re < 1` clause coming from mathlib's nonvanishing at
    `1 <= re`.

Consequently the soft layer's analytic hypothesis bundle is DISCHARGED
(`zetaPoleData`), and `zeta_landau_windowed_unconditional` —
Rubinstein's windowed Landau lemma for zeta — holds with no hypotheses
at all in the soft layer.

Corresponding classical material: ../classical/paper.tex §2 (the
statistic and its Mellin transform — the construction's `laplace`
field is the paper's Prop 2.2) and §5 (the certificate).
-/
import LandauWindows.Soft.CharFamily
import LandauWindows.Soft.PoleData
import LandauWindows.Soft.PoleDataConstruction
import LandauWindows.Soft.LFunctionConj
import LandauWindows.Soft.ZetaWindowed
import LandauWindows.Statement

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace LandauWindows

open Deduction Formalism

/-! ### The trivial family -/

/-- The trivial character family: the conductor-1 (trivial) Dirichlet
character alone, with weight 1.  Its statistic is `Gz` and its zero set
is the strip zero set of zeta.  (Reducible so that `NeZero (Ftriv.N _)`
can be found by instance search through the structure projections.) -/
@[reducible]
def Ftriv : CharFamily where
  ι := Unit
  N := fun _ => 1
  nz := fun _ => inferInstance
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

/-! ### Bridge: the statistic -/

/-- The conductor-1 character is `1` on every `n` (mod 1, everything
is a unit). -/
lemma modOne_char_apply (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n) = 1 := by
  have h1 : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [h1]

/-- The archive's `ramp` with constant weight `1` is the complex
embedding of `Formalism.Sz`. -/
lemma ramp_one_eq (y : ℝ) (hy : 0 < y) :
    ramp (fun _ => (1 : ℂ)) y = (Sz y : ℂ) := by
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  have hy0 : (0 : ℝ) ≤ y := hy.le
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  unfold ramp Sz
  rw [← Finset.sum_subset hsub ?_, Complex.ofReal_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y := by
      have h1 : (n : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn.2
      exact h1.trans hfl
    have hge : 1 ≤ y / n := by rw [le_div_iff₀ hn0, one_mul]; exact hny
    rw [max_eq_left (by linarith : 0 ≤ y / n - 1)]
    push_cast
    ring
  · intro n hn h'n
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc] at h'n
    have h0 : n = 0 := by omega
    subst h0
    simp

/-- The `Gchi` of the conductor-1 character is the complex embedding
of `Formalism.Gz`. -/
lemma Gchi_modOne_eq (y : ℝ) (hy : 0 < y) :
    Gchi (1 : DirichletCharacter ℂ 1) y = ((Gz y : ℝ) : ℂ) := by
  have hf : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n)
      = (fun _ => (1 : ℂ)) := funext modOne_char_apply
  unfold Gchi
  rw [if_pos rfl, hf, ramp_one_eq y hy]
  unfold Gz Sz
  push_cast
  ring

/-- The trivial family's statistic is `Gz`. -/
lemma Gm_Ftriv_eq (y : ℝ) (hy : 0 < y) : Gm Ftriv y = Gz y := by
  have hsum : ∑ i, Ftriv.a i * (Gchi (Ftriv.χ i) y).re
      = (Gchi (Ftriv.χ Unit.unit) y).re := by
    simp
  unfold Gm
  rw [hsum]
  simp only [Gchi_modOne_eq y hy]
  simp

/-- Hence the log-variable statistic is `gz`. -/
lemma gm_Ftriv_eq : gm Ftriv = gz := by
  funext u
  exact Gm_Ftriv_eq _ (Real.exp_pos u)

/-! ### Bridge: the zero set -/

/-- The conductor-1 L-function is `riemannZeta` pointwise. -/
lemma LFunction_modOne_zeta (s : ℂ) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  rw [DirichletCharacter.LFunction_modOne_eq]

/-- The trivial family's zero set is the strip zero set of zeta. -/
lemma zeroSet_Ftriv_eq : zeroSet Ftriv = zetaStripZeros := by
  ext ρ
  constructor
  · rintro ⟨hρ, i, hi | hi⟩
    · simp only [Ftriv] at hi
      rw [LFunction_modOne_zeta] at hi
      by_cases h1 : 1 ≤ ρ.re
      · exact absurd hi (riemannZeta_ne_zero_of_one_le_re h1)
      · exact ⟨hi, hρ, not_le.mp h1⟩
    · simp only [Ftriv] at hi
      rw [LFunction_modOne_zeta] at hi
      have hinv : (1 : DirichletCharacter ℂ 1)⁻¹ = 1 := Subsingleton.elim _ _
      have hconj := LFunction_conj (1 : DirichletCharacter ℂ 1) ρ
      rw [hinv, LFunction_modOne_zeta, LFunction_modOne_zeta] at hconj
      rw [hi] at hconj
      have h0 : riemannZeta ρ = 0 := by
        have := (map_eq_zero (f := (starRingEnd ℂ))).mp (eq_comm.mp hconj)
        simpa using this
      by_cases h1 : 1 ≤ ρ.re
      · exact absurd h0 (riemannZeta_ne_zero_of_one_le_re h1)
      · exact ⟨h0, hρ, not_le.mp h1⟩
  · rintro ⟨hζ, hρ, -⟩
    refine ⟨hρ, Unit.unit, Or.inl ?_⟩
    simp only [Ftriv]
    rw [LFunction_modOne_zeta]
    exact hζ

/-! ### The discharge -/

/-- **The analytic hypothesis bundle, discharged.** The lifted
construction `Deduction.poleData` applied to the trivial family gives
`PoleData` for our `gz` over our `zetaStripZeros`.  This was the soft
layer's only hypothesis. -/
theorem zetaPoleData : ∃ Φ : ℂ → ℂ, PoleData gz Φ zetaStripZeros := by
  obtain ⟨Φ, hΦ⟩ := Deduction.poleData Ftriv
  rw [gm_Ftriv_eq, zeroSet_Ftriv_eq] at hΦ
  exact ⟨Φ, hΦ⟩

/-- **Rubinstein's windowed Landau lemma for ζ — unconditional (soft
layer).** If there are arbitrarily large `Y` with `Gz x ≤ C x ^ θ`
throughout `[Y, Y ^ (3/2)]`, then ζ has no zero with real part `> θ`.
No analytic hypotheses remain: the `ZetaPoleData` bundle is discharged
by `zetaPoleData` above, and everything else is the lifted abstract
`Deduction.landau_window` plus elementary bridges. -/
theorem zeta_landau_windowed_unconditional {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) {C : ℝ} (hC : 0 < C)
    (hceil : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)), Gz x ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  zeta_landau_windowed zetaPoleData hθ hθ1 hC hceil

end LandauWindows

end
