import LandauWindows.Shadow.Interval
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.LemmasAux

namespace LandauWindows.Shadow

def distance (left right : Int) : Int :=
  if left ≤ right then right - left else left - right

def gridIndex (left step point : Int) : Nat := ((point - left) / step).toNat

def gridAddress (left step : Int) (index : Nat) : Int := left + (index : Int) * step

theorem gridIndex_le {left right point step : Int} (hstep : 0 < step)
    (hpoint : point ≤ right) : gridIndex left step point ≤ gridIndex left step right := by
  have hdiv := Int.ediv_le_ediv hstep (Int.sub_le_sub_right hpoint left)
  exact Int.toNat_le_toNat hdiv

theorem gridIndex_spec {left right point step : Int} (hstep : 0 < step)
    (hleft : left ≤ point) (hright : point ≤ right) :
    gridIndex left step point ≤ gridIndex left step right ∧
      left ≤ gridAddress left step (gridIndex left step point) ∧
      gridAddress left step (gridIndex left step point) ≤ right ∧
      distance (gridAddress left step (gridIndex left step point)) point ≤ step := by
  have hdiv : 0 ≤ (point - left) / step := Int.ediv_nonneg (by omega) (by omega)
  have hmul := Int.mul_nonneg hdiv (Int.le_of_lt hstep)
  have hmod := Int.emod_nonneg (point - left) (Int.ne_of_gt hstep)
  have hmodlt := Int.emod_lt_of_pos (point - left) hstep
  have hidentity := Int.ediv_mul_add_emod (point - left) step
  refine ⟨gridIndex_le hstep hright, ?_⟩
  unfold gridAddress gridIndex
  rw [Int.toNat_of_nonneg hdiv]
  unfold distance
  have horder : left + (point - left) / step * step ≤ point := by omega
  rw [if_pos horder]
  constructor
  · omega
  · constructor <;> omega

theorem margin_survives_transport {point address peak lipschitz mesh threshold error value : Int}
    (hlipschitz : 0 ≤ lipschitz) (hnearby : distance address point ≤ mesh)
    (hpeak : threshold + error + lipschitz * mesh < peak)
    (hvalue : peak - lipschitz * distance address point ≤ value) :
    threshold + error < value := by
  have hproduct := Int.mul_le_mul_of_nonneg_left hnearby hlipschitz
  omega

def sampleGrid (left right step : Int) (enclose : Int → Interval) : List Sample :=
  (List.range (gridIndex left step right + 1)).map fun index =>
    let address := gridAddress left step index
    ⟨address, enclose address⟩

theorem grid_search_complete {left right point step peak lipschitz threshold error : Int}
    {enclose : Int → Interval} {value : Int → Int}
    (hstep : 0 < step) (hleft : left ≤ point) (hright : point ≤ right)
    (hlipschitz : 0 ≤ lipschitz)
    (hsound : ∀ sample ∈ sampleGrid left right step enclose,
      sample.enclosure.Contains (value sample.address))
    (hwidth : ∀ sample ∈ sampleGrid left right step enclose, sample.enclosure.width ≤ error)
    (hvalue : ∀ sample ∈ sampleGrid left right step enclose,
      peak - lipschitz * distance sample.address point ≤ value sample.address)
    (hpeak : threshold + error + lipschitz * step < peak) :
    firstAbove threshold (sampleGrid left right step enclose) ≠ none := by
  have hspec := gridIndex_spec hstep hleft hright
  let witness : Sample :=
    ⟨gridAddress left step (gridIndex left step point),
      enclose (gridAddress left step (gridIndex left step point))⟩
  have hmem : witness ∈ sampleGrid left right step enclose := by
    apply List.mem_map.mpr
    exact ⟨gridIndex left step point, List.mem_range.mpr (Nat.lt_succ_of_le hspec.1), rfl⟩
  apply firstAbove_complete_of_margin hsound hwidth
  exact ⟨witness, hmem,
    margin_survives_transport hlipschitz hspec.2.2.2 hpeak (hvalue witness hmem)⟩

end LandauWindows.Shadow
