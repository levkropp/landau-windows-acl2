import LandauWindows.Soft.SignalBounds

namespace LandauWindows.CertificateGeometry

def signalSamples (addresses : List ℚ) (ceiling : ℚ) (numerator denominator : ℕ)
    (error : ℚ) : List Bounds :=
  addresses.map (fun address => signalBounds address ceiling numerator denominator error)

def firstPositive : List Bounds → Option (ℕ × Bounds)
  | [] => none
  | first :: rest =>
      if 0 < first.lower then some (0, first)
      else match firstPositive rest with
      | none => none
      | some (index, bounds) => some (index + 1, bounds)

theorem firstPositive_sound (samples : List Bounds) (index : ℕ) (bounds : Bounds)
    (hfound : firstPositive samples = some (index, bounds)) :
    index < samples.length ∧ samples[index]? = some bounds ∧ 0 < bounds.lower := by
  induction samples generalizing index bounds with
  | nil => simp [firstPositive] at hfound
  | cons first rest ih =>
      dsimp only [firstPositive] at hfound
      split_ifs at hfound with hpositive
      · cases hfound
        exact ⟨by simp, by simp, hpositive⟩
      · cases hrest : firstPositive rest with
        | none => simp [hrest] at hfound
        | some result =>
            rcases result with ⟨nextIndex, nextBounds⟩
            simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hfound
            rcases hfound with ⟨rfl, rfl⟩
            rcases ih nextIndex nextBounds hrest with ⟨hbound, hsample, hsign⟩
            exact ⟨by simp; omega, by simpa using hsample, hsign⟩

theorem firstPositive_complete (samples : List Bounds)
    (hpositive : ∃ bounds ∈ samples, 0 < bounds.lower) :
    ∃ found, firstPositive samples = some found := by
  induction samples with
  | nil => simpa using hpositive
  | cons first rest ih =>
      by_cases hfirst : 0 < first.lower
      · exact ⟨(0, first), by simp [firstPositive, hfirst]⟩
      · have hrest : ∃ bounds ∈ rest, 0 < bounds.lower := by
          rcases hpositive with ⟨bounds, hmember, hsign⟩
          rcases List.mem_cons.mp hmember with heq | hmember
          · subst bounds; exact False.elim (hfirst hsign)
          · exact ⟨bounds, hmember, hsign⟩
        obtain ⟨⟨index, bounds⟩, hfound⟩ := ih hrest
        exact ⟨(index + 1, bounds), by simp [firstPositive, hfirst, hfound]⟩

def signalSearch (addresses : List ℚ) (ceiling : ℚ) (numerator denominator : ℕ)
    (error : ℚ) : Option (ℕ × Bounds) :=
  firstPositive (signalSamples addresses ceiling numerator denominator error)

theorem signalSearch_sound (addresses : List ℚ) (ceiling error : ℚ)
    (numerator denominator index : ℕ) (bounds : Bounds)
    (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (haddresses : ∀ address ∈ addresses, 1 ≤ address)
    (hfound : signalSearch addresses ceiling numerator denominator error = some (index, bounds)) :
    ∃ address : ℚ, addresses[index]? = some address ∧
      bounds = signalBounds address ceiling numerator denominator error ∧
      (ceiling : ℝ) * (address : ℝ) ^ ((numerator : ℝ) / denominator) < Formalism.Gz address := by
  rcases firstPositive_sound _ index bounds hfound with ⟨_, hsample, hsign⟩
  simp only [signalSamples, List.getElem?_map] at hsample
  rcases Option.map_eq_some_iff.mp hsample with ⟨address, haddress, hbounds⟩
  refine ⟨address, haddress, hbounds.symm, ?_⟩
  have hmember : address ∈ addresses := List.mem_of_getElem? haddress
  apply signalBounds_violation address ceiling error numerator denominator
    (haddresses address hmember) hdegree hexponent
  simpa only [hbounds] using hsign

/- The width conditions are rational inequalities proved for every computed
sample by ACL2. The genuinely analytic premise remaining here is transport
from a peak of the actual signal, not an assumed successful search. -/
theorem signalSearch_complete_of_peak (addresses : List ℚ) (ceiling error step lipschitz : ℚ)
    (numerator denominator : ℕ) (point peak : ℝ)
    (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (haddresses : ∀ address ∈ addresses, 1 ≤ address)
    (hlipschitz : 0 ≤ lipschitz)
    (hnearby : ∃ address ∈ addresses, |point - (address : ℝ)| ≤ (step : ℝ))
    (hmargin : (error : ℝ) + (lipschitz : ℝ) * step < peak)
    (htransport : ∀ address ∈ addresses,
      peak - (lipschitz : ℝ) * |point - (address : ℝ)| ≤
        Formalism.Gz address - (ceiling : ℝ) * (address : ℝ) ^ ((numerator : ℝ) / denominator))
    (hwidth : ∀ address ∈ addresses,
      (signalBounds address ceiling numerator denominator error).upper -
        (signalBounds address ceiling numerator denominator error).lower ≤ error) :
    ∃ found, signalSearch addresses ceiling numerator denominator error = some found := by
  obtain ⟨address, hmember, hnear⟩ := hnearby
  have hsample := signalBounds_sound address ceiling error numerator denominator
    (haddresses address hmember) hdegree hexponent
  have hwidthR : ((signalBounds address ceiling numerator denominator error).upper : ℝ) -
      (signalBounds address ceiling numerator denominator error).lower ≤ (error : ℝ) := by
    exact_mod_cast hwidth address hmember
  have hL : (0 : ℝ) ≤ lipschitz := by exact_mod_cast hlipschitz
  have hproduct := mul_le_mul_of_nonneg_left hnear hL
  have hsignR : (0 : ℝ) < (signalBounds address ceiling numerator denominator error).lower := by
    linarith [htransport address hmember, hsample.2]
  have hsign : 0 < (signalBounds address ceiling numerator denominator error).lower := by
    exact_mod_cast hsignR
  apply firstPositive_complete
  refine ⟨signalBounds address ceiling numerator denominator error, ?_, hsign⟩
  exact List.mem_map.mpr ⟨address, hmember, rfl⟩

/- ACL2's `lw-landau-search-failure-signal-ceiling` supplies this finite
upper-endpoint inequality at every rational point of its window. This is
its meaning for the actual statistic, with the explicit ceiling buffer. -/
theorem evaluated_ceiling_sound (point ceiling : ℚ) (numerator denominator : ℕ)
    (hpoint : 1 ≤ point) (hdegree : 0 < denominator) (hexponent : numerator ≤ denominator)
    (hupper : (signalBounds point ceiling numerator denominator (1 / 4)).upper ≤ 1) :
    Formalism.Gz point ≤ ((ceiling : ℝ) + 1) *
      (point : ℝ) ^ ((numerator : ℝ) / denominator) := by
  have hsignal := signalBounds_sound point ceiling (1 / 4) numerator denominator
    hpoint hdegree hexponent
  have hu : ((signalBounds point ceiling numerator denominator (1 / 4)).upper : ℝ) ≤ 1 := by
    exact_mod_cast hupper
  have hp : (1 : ℝ) ≤ (point : ℝ) ^ ((numerator : ℝ) / denominator) :=
    Real.one_le_rpow (by exact_mod_cast hpoint) (by positivity)
  nlinarith [hsignal.2]

end LandauWindows.CertificateGeometry
