/-
Axiom audit (soft layer), checked on every `lake build`.

Phase-2 discipline (`../docs/roadmap.md`): the *effective shadow's* main
theorem must eventually depend on no more than the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`).  The soft layer is
expected to use them (it is classical mathlib mathematics); the points
of this file are (i) to make the dependency explicit on every build,
(ii) to catch accidental `sorry`s (`sorryAx`) anywhere in the chain,
and (iii) to record, per theorem, whether it is lifted or ours.
-/
import LandauWindows.Statement
import LandauWindows.Soft.ZetaWindowed
import LandauWindows.Soft.ZetaPoleData
import LandauWindows.T1

-- The lifted abstract windowed Landau theorem (ours = the lift itself):
#print axioms Deduction.landau_window

-- Our ζ-instantiation (proved modulo the named hypothesis ZetaPoleData):
#print axioms LandauWindows.zeta_landau_windowed
#print axioms LandauWindows.windowHypU_of_ceiling

-- The discharge (ours): the analytic bundle, proved from the lifted
-- construction at the trivial family:
#print axioms LandauWindows.zetaPoleData

-- The unconditional windowed Landau lemma for ζ (ours):
#print axioms LandauWindows.zeta_landau_windowed_unconditional

-- T1 in the soft layer (ours), derived logically from the above:
#print axioms LandauWindows.t1Soft

-- Statement-only (definitions of Props; no proofs to audit):
#print axioms Formalism.ZetaLandau
#print axioms LandauWindows.ZetaPoleData
