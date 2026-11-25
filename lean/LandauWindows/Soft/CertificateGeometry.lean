import Mathlib

namespace LandauWindows.CertificateGeometry

structure Bounds where
  lower : ℚ
  upper : ℚ

namespace Bounds

def Contains (bounds : Bounds) (value : ℝ) : Prop :=
  (bounds.lower : ℝ) ≤ value ∧ value ≤ (bounds.upper : ℝ)

def point (value : ℚ) : Bounds := ⟨value, value⟩

def add (left right : Bounds) : Bounds :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

def sub (left right : Bounds) : Bounds :=
  ⟨left.lower - right.upper, left.upper - right.lower⟩

def square (bounds : Bounds) : Bounds :=
  ⟨if bounds.lower ≤ 0 ∧ 0 ≤ bounds.upper then 0
    else min (bounds.lower * bounds.lower) (bounds.upper * bounds.upper),
    max (bounds.lower * bounds.lower) (bounds.upper * bounds.upper)⟩

theorem point_sound (value : ℚ) : (point value).Contains (value : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_sound {left right : Bounds} {leftValue rightValue : ℝ}
    (hleft : left.Contains leftValue) (hright : right.Contains rightValue) :
    (add left right).Contains (leftValue + rightValue) := by
  rcases hleft with ⟨hleftLower, hleftUpper⟩
  rcases hright with ⟨hrightLower, hrightUpper⟩
  constructor <;> dsimp [add] <;> push_cast <;> linarith

theorem sub_sound {left right : Bounds} {leftValue rightValue : ℝ}
    (hleft : left.Contains leftValue) (hright : right.Contains rightValue) :
    (sub left right).Contains (leftValue - rightValue) := by
  rcases hleft with ⟨hleftLower, hleftUpper⟩
  rcases hright with ⟨hrightLower, hrightUpper⟩
  constructor <;> dsimp [sub] <;> push_cast <;> linarith

theorem square_sound {bounds : Bounds} {value : ℝ} (hvalue : bounds.Contains value) :
    bounds.square.Contains (value * value) := by
  rcases hvalue with ⟨hlower, hupper⟩
  have hmax : value * value ≤
      max ((bounds.lower : ℝ) * (bounds.lower : ℝ))
        ((bounds.upper : ℝ) * (bounds.upper : ℝ)) := by
    by_cases hsign : 0 ≤ value
    · exact (show value * value ≤ (bounds.upper : ℝ) * (bounds.upper : ℝ) by nlinarith).trans
        (le_max_right _ _)
    · exact (show value * value ≤ (bounds.lower : ℝ) * (bounds.lower : ℝ) by nlinarith).trans
        (le_max_left _ _)
  constructor
  · dsimp [square]
    split_ifs with hcross
    · simp only [Rat.cast_zero]
      exact mul_self_nonneg value
    · push_cast
      by_cases hsign : 0 ≤ (bounds.lower : ℝ)
      · exact (min_le_left _ _).trans (by nlinarith)
      · have hlowerQ : bounds.lower ≤ 0 := by exact_mod_cast (le_of_not_ge hsign)
        have hupperQ : bounds.upper < 0 := lt_of_not_ge fun hu => hcross ⟨hlowerQ, hu⟩
        have hupperR : (bounds.upper : ℝ) < 0 := by exact_mod_cast hupperQ
        exact (min_le_right _ _).trans (by nlinarith)
  · dsimp [square]
    push_cast
    exact hmax

end Bounds

structure Box where
  real : Bounds
  imag : Bounds

def Box.Contains (box : Box) (point : ℂ) : Prop :=
  box.real.Contains point.re ∧ box.imag.Contains point.im

def centre (sigma height : ℚ) : ℂ := ⟨(sigma : ℝ), (height : ℝ)⟩

def Box.distanceBounds (box : Box) (sigma height : ℚ) : Bounds :=
  ((Bounds.point sigma).sub box.real).square.add ((Bounds.point height).sub box.imag).square

theorem distanceBounds_sound {box : Box} {point : ℂ} (sigma height : ℚ)
    (hpoint : box.Contains point) :
    (box.distanceBounds sigma height).Contains (‖centre sigma height - point‖ ^ 2) := by
  have hreal := Bounds.square_sound (Bounds.sub_sound (Bounds.point_sound sigma) hpoint.1)
  have himag := Bounds.square_sound (Bounds.sub_sound (Bounds.point_sound height) hpoint.2)
  have hsum := Bounds.add_sound hreal himag
  simpa only [Box.distanceBounds, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, centre] using hsum

def circleCheck (sigma height radiusSquared : ℚ) (selected : Box) (others : List Box) : Bool :=
  decide (0 < radiusSquared) && decide ((selected.distanceBounds sigma height).upper < radiusSquared) &&
    others.all (fun box => decide (radiusSquared < (box.distanceBounds sigma height).lower))

theorem circleCheck_contains_selected {sigma height radiusSquared : ℚ}
    {selected : Box} {others : List Box} {point : ℂ}
    (hcheck : circleCheck sigma height radiusSquared selected others = true)
    (hpoint : selected.Contains point) :
    ‖centre sigma height - point‖ ^ 2 < (radiusSquared : ℝ) := by
  have hchecked := hcheck
  simp only [circleCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchecked
  have hupper := (distanceBounds_sound sigma height hpoint).2
  have hradius : ((selected.distanceBounds sigma height).upper : ℝ) < (radiusSquared : ℝ) := by
    exact_mod_cast hchecked.1.2
  exact hupper.trans_lt hradius

theorem circleCheck_excludes_others {sigma height radiusSquared : ℚ}
    {selected box : Box} {others : List Box} {point : ℂ}
    (hcheck : circleCheck sigma height radiusSquared selected others = true)
    (hbox : box ∈ others) (hpoint : box.Contains point) :
    (radiusSquared : ℝ) < ‖centre sigma height - point‖ ^ 2 := by
  have hchecked := hcheck
  simp only [circleCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchecked
  have hlower := (distanceBounds_sound sigma height hpoint).1
  have hradius : (radiusSquared : ℝ) < ((box.distanceBounds sigma height).lower : ℝ) := by
    exact_mod_cast (hchecked.2 box hbox)
  exact hradius.trans_le hlower

theorem circleCheck_isolates {sigma height radiusSquared : ℚ}
    {selected : Box} {others : List Box} {zeros : Set ℂ} {pole : ℂ}
    (hcheck : circleCheck sigma height radiusSquared selected others = true)
    (hpoleZero : pole ∈ zeros)
    (hpole : selected.Contains pole)
    (hunique : ∀ point ∈ zeros, selected.Contains point → point = pole)
    (hcover : ∀ point ∈ zeros, selected.Contains point ∨ ∃ box ∈ others, box.Contains point) :
    pole ∈ zeros ∧ ‖centre sigma height - pole‖ ^ 2 < (radiusSquared : ℝ) ∧
      ∀ point ∈ zeros, ‖centre sigma height - point‖ ^ 2 < (radiusSquared : ℝ) → point = pole := by
  refine ⟨hpoleZero, circleCheck_contains_selected hcheck hpole, ?_⟩
  intro point hzero hinside
  rcases hcover point hzero with hselected | ⟨box, hbox, hpoint⟩
  · exact hunique point hzero hselected
  · have houtside := circleCheck_excludes_others hcheck hbox hpoint
    linarith

theorem window_endpoint_sound {start : ℚ} {bounds : Bounds}
    (hstart : 1 ≤ start) (hlower : 0 ≤ bounds.lower) (horder : bounds.lower ≤ bounds.upper)
    (hlowerSquare : bounds.lower * bounds.lower ≤ start * start * start)
    (hupperSquare : start * start * start ≤ bounds.upper * bounds.upper) :
    bounds.Contains ((start : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hstartR : (1 : ℝ) ≤ (start : ℝ) := by exact_mod_cast hstart
  have hstartNonneg : 0 ≤ (start : ℝ) := by linarith
  have hlowerR : (0 : ℝ) ≤ (bounds.lower : ℝ) := by exact_mod_cast hlower
  have horderR : (bounds.lower : ℝ) ≤ (bounds.upper : ℝ) := by exact_mod_cast horder
  have hpower : ((start : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (start : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hstartNonneg]
    norm_num
  have hnonneg := Real.rpow_nonneg hstartNonneg ((3 : ℝ) / 2)
  have hlowerSquareR : (bounds.lower : ℝ) * (bounds.lower : ℝ) ≤
      (start : ℝ) * (start : ℝ) * (start : ℝ) := by exact_mod_cast hlowerSquare
  have hupperSquareR : (start : ℝ) * (start : ℝ) * (start : ℝ) ≤
      (bounds.upper : ℝ) * (bounds.upper : ℝ) := by exact_mod_cast hupperSquare
  constructor <;> nlinarith

def lastAddress : List ℚ → ℚ
  | [] => 0
  | [address] => address
  | _ :: rest => lastAddress rest

def Mesh (step : ℚ) : List ℚ → Prop
  | [] => False
  | [_] => True
  | left :: right :: rest => left ≤ right ∧ right - left ≤ step ∧ Mesh step (right :: rest)

theorem mesh_covers_real {addresses : List ℚ} {step : ℚ} (hmesh : Mesh step addresses)
    (hstep : 0 ≤ step) {point : ℝ}
    (hleft : (addresses.headD 0 : ℝ) ≤ point) (hright : point ≤ (lastAddress addresses : ℝ)) :
    ∃ address ∈ addresses, |point - (address : ℝ)| ≤ (step : ℝ) := by
  induction addresses with
  | nil => exact False.elim hmesh
  | cons first rest ih =>
      cases rest with
      | nil =>
          refine ⟨first, by simp, ?_⟩
          have heq : point = (first : ℝ) := by simpa [lastAddress] using le_antisymm hright hleft
          rw [heq, sub_self, abs_zero]
          exact_mod_cast hstep
      | cons second rest =>
          by_cases hpoint : point ≤ (second : ℝ)
          · refine ⟨second, by simp, ?_⟩
            have hgap : (second : ℝ) - (first : ℝ) ≤ (step : ℝ) := by exact_mod_cast hmesh.2.1
            have hstepR : (0 : ℝ) ≤ (step : ℝ) := by exact_mod_cast hstep
            have hfirst : (first : ℝ) ≤ point := by simpa using hleft
            apply abs_le.mpr
            constructor <;> linarith
          · have hsecond : (second : ℝ) ≤ point := le_of_not_ge hpoint
            obtain ⟨address, hmem, hnearby⟩ := ih hmesh.2.2 (by simpa using hsecond) hright
            exact ⟨address, List.mem_cons_of_mem _ hmem, hnearby⟩

theorem lastAddress_mem {addresses : List ℚ} (haddresses : addresses ≠ []) :
    lastAddress addresses ∈ addresses := by
  induction addresses with
  | nil => exact False.elim (haddresses rfl)
  | cons first rest ih =>
      cases rest with
      | nil => simp [lastAddress]
      | cons second rest =>
          exact List.mem_cons_of_mem _ (ih (by simp))

theorem roundedMesh_covers_real_window {addresses : List ℚ} {start step : ℚ} {bounds : Bounds}
    (hmesh : Mesh step addresses) (hstep : 0 ≤ step)
    (hfirst : addresses.headD 0 = start) (hlast : lastAddress addresses = bounds.lower)
    (hendpoint : bounds.Contains ((start : ℝ) ^ ((3 : ℝ) / 2)))
    (hwidth : bounds.upper - bounds.lower ≤ step) {point : ℝ}
    (hpoint : point ∈ Set.Icc (start : ℝ) ((start : ℝ) ^ ((3 : ℝ) / 2))) :
    ∃ address ∈ addresses, |point - (address : ℝ)| ≤ (step : ℝ) := by
  by_cases htail : point ≤ (bounds.lower : ℝ)
  · apply mesh_covers_real hmesh hstep
    · rw [hfirst]
      exact hpoint.1
    · rw [hlast]
      exact htail
  · have hnonempty : addresses ≠ [] := by
      intro hempty
      subst addresses
      exact hmesh
    refine ⟨bounds.lower, hlast ▸ lastAddress_mem hnonempty, ?_⟩
    have hwidthR : (bounds.upper : ℝ) - (bounds.lower : ℝ) ≤ (step : ℝ) := by exact_mod_cast hwidth
    have hstepR : (0 : ℝ) ≤ (step : ℝ) := by exact_mod_cast hstep
    apply abs_le.mpr
    constructor <;> linarith [hpoint.2, hendpoint.2]

end LandauWindows.CertificateGeometry
