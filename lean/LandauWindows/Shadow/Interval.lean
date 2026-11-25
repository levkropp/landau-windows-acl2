import Init.Data.Int.Lemmas
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Omega

/-!
Intervals contain integer numerators at a common positive denominator, kept explicit
by the caller. Addition and subtraction preserve that scale; scaling here is by an
integer. This representation avoids normalized rational numbers and their proof
dependencies. Real-valued interpretation belongs in the soft layer.
-/

namespace LandauWindows.Shadow

structure Interval where
  lower : Int
  upper : Int
  deriving Repr, DecidableEq

namespace Interval

def Contains (bounds : Interval) (value : Int) : Prop :=
  bounds.lower ≤ value ∧ value ≤ bounds.upper

def width (bounds : Interval) : Int := bounds.upper - bounds.lower

def point (value : Int) : Interval := ⟨value, value⟩

def add (left right : Interval) : Interval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

def sub (left right : Interval) : Interval :=
  ⟨left.lower - right.upper, left.upper - right.lower⟩

def scale (coefficient : Int) (bounds : Interval) : Interval :=
  if 0 ≤ coefficient then
    ⟨coefficient * bounds.lower, coefficient * bounds.upper⟩
  else
    ⟨coefficient * bounds.upper, coefficient * bounds.lower⟩

theorem contains_point (value : Int) : (point value).Contains value :=
  ⟨Int.le_refl _, Int.le_refl _⟩

theorem contains_add {left right : Interval} {leftValue rightValue : Int}
    (hleft : left.Contains leftValue) (hright : right.Contains rightValue) :
    (add left right).Contains (leftValue + rightValue) :=
  ⟨Int.add_le_add hleft.1 hright.1, Int.add_le_add hleft.2 hright.2⟩

theorem contains_sub {left right : Interval} {leftValue rightValue : Int}
    (hleft : left.Contains leftValue) (hright : right.Contains rightValue) :
    (sub left right).Contains (leftValue - rightValue) :=
  ⟨Int.sub_le_sub hleft.1 hright.2, Int.sub_le_sub hleft.2 hright.1⟩

theorem contains_scale (coefficient : Int) {bounds : Interval} {value : Int}
    (hvalue : bounds.Contains value) :
    (scale coefficient bounds).Contains (coefficient * value) := by
  unfold scale
  by_cases hsign : 0 ≤ coefficient
  · rw [if_pos hsign]
    exact ⟨Int.mul_le_mul_of_nonneg_left hvalue.1 hsign,
      Int.mul_le_mul_of_nonneg_left hvalue.2 hsign⟩
  · rw [if_neg hsign]
    exact ⟨Int.mul_le_mul_of_nonpos_left (by omega) hvalue.2,
      Int.mul_le_mul_of_nonpos_left (by omega) hvalue.1⟩

theorem lower_gt_of_margin {bounds : Interval} {value threshold error : Int}
    (hvalue : bounds.Contains value) (hwidth : bounds.width ≤ error)
    (hmargin : threshold + error < value) : threshold < bounds.lower := by
  unfold Contains at hvalue
  unfold width at hwidth
  omega

end Interval

structure Sample where
  address : Int
  enclosure : Interval
  deriving Repr, DecidableEq

def firstAbove (threshold : Int) : List Sample → Option Sample
  | [] => none
  | sample :: samples =>
      if threshold < sample.enclosure.lower then some sample else firstAbove threshold samples

theorem firstAbove_sound {threshold : Int} {samples : List Sample} {found : Sample}
    (hfound : firstAbove threshold samples = some found) :
    found ∈ samples ∧ threshold < found.enclosure.lower := by
  induction samples with
  | nil => simp [firstAbove] at hfound
  | cons sample samples ih =>
      simp only [firstAbove] at hfound
      by_cases hhead : threshold < sample.enclosure.lower
      · rw [if_pos hhead] at hfound
        cases Option.some.inj hfound
        exact ⟨List.mem_cons_self, hhead⟩
      · rw [if_neg hhead] at hfound
        obtain ⟨hmem, hlower⟩ := ih hfound
        exact ⟨List.mem_cons_of_mem _ hmem, hlower⟩

theorem firstAbove_complete {threshold : Int} {samples : List Sample}
    (hwitness : ∃ sample ∈ samples, threshold < sample.enclosure.lower) :
    firstAbove threshold samples ≠ none := by
  induction samples with
  | nil => simp at hwitness
  | cons sample samples ih =>
      simp only [firstAbove]
      by_cases hhead : threshold < sample.enclosure.lower
      · rw [if_pos hhead]
        exact Option.some_ne_none _
      · rw [if_neg hhead]
        apply ih
        obtain ⟨witness, hmem, hbound⟩ := hwitness
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst witness
          exact False.elim (hhead hbound)
        · exact ⟨witness, hmem, hbound⟩

theorem firstAbove_value_gt {threshold : Int} {samples : List Sample} {found : Sample}
    {value : Int → Int} (hsound : ∀ sample ∈ samples,
      sample.enclosure.Contains (value sample.address))
    (hfound : firstAbove threshold samples = some found) :
    threshold < value found.address := by
  obtain ⟨hmem, hbound⟩ := firstAbove_sound hfound
  exact Int.lt_of_lt_of_le hbound (hsound found hmem).1

theorem firstAbove_complete_of_margin {threshold error : Int} {samples : List Sample}
    {value : Int → Int} (hsound : ∀ sample ∈ samples,
      sample.enclosure.Contains (value sample.address))
    (hwidth : ∀ sample ∈ samples, sample.enclosure.width ≤ error)
    (hpeak : ∃ sample ∈ samples, threshold + error < value sample.address) :
    firstAbove threshold samples ≠ none := by
  apply firstAbove_complete
  obtain ⟨sample, hmem, hmargin⟩ := hpeak
  exact ⟨sample, hmem, Interval.lower_gt_of_margin (hsound sample hmem)
    (hwidth sample hmem) hmargin⟩

end LandauWindows.Shadow
