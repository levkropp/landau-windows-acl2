import LandauWindows.Shadow.Interval
import LandauWindows.Shadow.Grid

#print axioms LandauWindows.Shadow.Interval.contains_point
#print axioms LandauWindows.Shadow.Interval.contains_add
#print axioms LandauWindows.Shadow.Interval.contains_sub
#print axioms LandauWindows.Shadow.Interval.contains_scale
#print axioms LandauWindows.Shadow.Interval.lower_gt_of_margin
#print axioms LandauWindows.Shadow.firstAbove_sound
#print axioms LandauWindows.Shadow.firstAbove_complete
#print axioms LandauWindows.Shadow.firstAbove_value_gt
#print axioms LandauWindows.Shadow.firstAbove_complete_of_margin
#print axioms LandauWindows.Shadow.gridIndex_le
#print axioms LandauWindows.Shadow.gridIndex_spec
#print axioms LandauWindows.Shadow.margin_survives_transport
#print axioms LandauWindows.Shadow.grid_search_complete

run_cmd do
  let theorems := [
    ``LandauWindows.Shadow.Interval.contains_point,
    ``LandauWindows.Shadow.Interval.contains_add,
    ``LandauWindows.Shadow.Interval.contains_sub,
    ``LandauWindows.Shadow.Interval.contains_scale,
    ``LandauWindows.Shadow.Interval.lower_gt_of_margin,
    ``LandauWindows.Shadow.firstAbove_sound,
    ``LandauWindows.Shadow.firstAbove_complete,
    ``LandauWindows.Shadow.firstAbove_value_gt,
    ``LandauWindows.Shadow.firstAbove_complete_of_margin,
    ``LandauWindows.Shadow.gridIndex_le,
    ``LandauWindows.Shadow.gridIndex_spec,
    ``LandauWindows.Shadow.margin_survives_transport,
    ``LandauWindows.Shadow.grid_search_complete]
  for theoremName in theorems do
    let dependencies ← Lean.collectAxioms theoremName
    for dependency in dependencies do
      unless dependency == ``propext || dependency == ``Quot.sound do
        throwError "Shadow theorem {theoremName} depends on forbidden axiom {dependency}"
