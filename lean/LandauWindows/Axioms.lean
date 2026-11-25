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
import LandauWindows.Soft.ZeroFreeOfRpowWindow
import LandauWindows.Soft.ZetaLandau
import LandauWindows.Soft.CertificateGeometry
import LandauWindows.Soft.EulerBounds
import LandauWindows.Soft.RpowBounds
import LandauWindows.Soft.PrimePowers
import LandauWindows.Soft.SignalBounds
import LandauWindows.Soft.SignalSearch
import LandauWindows.Soft.SignalWindow
import LandauWindows.Soft.KernelBounds
import LandauWindows.Soft.PhaseBounds
import LandauWindows.Soft.LogSignal
import LandauWindows.Soft.SpatialBounds
import LandauWindows.Soft.KernelSpatial
import LandauWindows.Soft.MellinSpatial
import LandauWindows.Soft.MellinPartitions
import LandauWindows.Soft.MellinTail
import LandauWindows.Soft.MellinIntegral
import LandauWindows.Soft.MellinQuadrature
import LandauWindows.Soft.WindowIndex
import LandauWindows.T1

-- The lifted abstract windowed Landau theorem (ours = the lift itself):
#print axioms Deduction.landau_window

-- The lifted family-level finale (windowed ceilings on the family
-- statistic give zero-freeness for every character of the family):
#print axioms Deduction.lemmaL
#print axioms Deduction.zeroFree_of_rpow_window

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

-- The mirror (s₀ = -1) direction and the full archive statements
-- (ours), including the now-discharged real nonvanishing input:
#print axioms LandauWindows.riemannZeta₁_eq_fractionalPart
#print axioms LandauWindows.riemannZeta_eq_fractionalPart
#print axioms LandauWindows.riemannZeta_re_neg_of_mem_Ioo
#print axioms LandauWindows.riemannZeta_ne_zero_of_mem_Ioo
#print axioms LandauWindows.zetaNoRealStripZeros
#print axioms LandauWindows.poleData_neg
#print axioms LandauWindows.zeta_landau_windowed_floor
#print axioms LandauWindows.zeta_landau
#print axioms LandauWindows.zeta_landau_eps
#print axioms LandauWindows.CertificateGeometry.circleCheck_isolates
#print axioms LandauWindows.CertificateGeometry.roundedMesh_covers_real_window
#print axioms LandauWindows.CertificateGeometry.computedLogBounds_sound
#print axioms LandauWindows.CertificateGeometry.computedEulerBounds_sound
#print axioms LandauWindows.CertificateGeometry.computedRpowBounds_sound
#print axioms LandauWindows.CertificateGeometry.mangoldtBounds_sound
#print axioms LandauWindows.CertificateGeometry.signalBounds_sound
#print axioms LandauWindows.CertificateGeometry.signalBounds_violation
#print axioms LandauWindows.CertificateGeometry.signalSearch_sound
#print axioms LandauWindows.CertificateGeometry.signalSearch_complete_of_peak
#print axioms LandauWindows.CertificateGeometry.evaluated_ceiling_sound
#print axioms LandauWindows.CertificateGeometry.Gz_continuousOn_Icc
#print axioms LandauWindows.CertificateGeometry.rational_ceiling_extends
#print axioms LandauWindows.CertificateGeometry.evaluated_window_ceiling_sound
#print axioms LandauWindows.CertificateGeometry.evaluated_landau_window_ceiling_sound
#print axioms LandauWindows.CertificateGeometry.computedExpBounds_sound
#print axioms LandauWindows.CertificateGeometry.computedExpNegBounds_sound
#print axioms LandauWindows.CertificateGeometry.kernelWeightBounds_sound
#print axioms LandauWindows.CertificateGeometry.phaseValue_norm
#print axioms LandauWindows.CertificateGeometry.phaseValue_exp_bound
#print axioms LandauWindows.CertificateGeometry.computedExpBounds_width
#print axioms LandauWindows.CertificateGeometry.Gz_lipschitz
#print axioms LandauWindows.CertificateGeometry.logSignalBounds_sound
#print axioms LandauWindows.CertificateGeometry.exp_spatial_bound
#print axioms LandauWindows.CertificateGeometry.logSignal_spatial_bound
#print axioms LandauWindows.CertificateGeometry.logSignalBounds_spatial_transport
#print axioms LandauWindows.CertificateGeometry.logSignalModulus_sound
#print axioms LandauWindows.CertificateGeometry.realKernelWeight_spatial_bound
#print axioms LandauWindows.CertificateGeometry.kernelWeightBounds_spatial_transport
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_rat
#print axioms LandauWindows.CertificateGeometry.mellinSignalSpatialCap_sound
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_spatial_bound
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_continuousOn
#print axioms LandauWindows.CertificateGeometry.mellinDyadicSum_sound
#print axioms LandauWindows.CertificateGeometry.mellinBoundedIntegral_sound
#print axioms LandauWindows.CertificateGeometry.Gz_abs_quadratic
#print axioms LandauWindows.CertificateGeometry.kernel_inverse_square_bound
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_inverse_square
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_tail_bound
#print axioms LandauWindows.CertificateGeometry.mellinTailCutoff_adequate
#print axioms LandauWindows.CertificateGeometry.realMellinIntegrand_integrableOn
#print axioms LandauWindows.CertificateGeometry.mellinIntegral_sound
#print axioms LandauWindows.CertificateGeometry.mellinIntegral_cauchy
#print axioms LandauWindows.CertificateGeometry.mellinWeightedValue_eq
#print axioms LandauWindows.CertificateGeometry.mellinSample_sound
#print axioms LandauWindows.CertificateGeometry.mellinSum_sound
#print axioms LandauWindows.CertificateGeometry.windowIndexCheck_sound

-- Fail the build if any audited proof acquires an extra assumption.
-- In particular, printing a sorryAx warning alone is not an adequate guard.
run_cmd do
  let theoremNames := [
    ``Deduction.landau_window,
    ``Deduction.lemmaL,
    ``Deduction.zeroFree_of_rpow_window,
    ``LandauWindows.zeta_landau_windowed,
    ``LandauWindows.windowHypU_of_ceiling,
    ``LandauWindows.zetaPoleData,
    ``LandauWindows.zeta_landau_windowed_unconditional,
    ``LandauWindows.t1Soft,
    ``LandauWindows.riemannZeta₁_eq_fractionalPart,
    ``LandauWindows.riemannZeta_eq_fractionalPart,
    ``LandauWindows.riemannZeta_re_neg_of_mem_Ioo,
    ``LandauWindows.riemannZeta_ne_zero_of_mem_Ioo,
    ``LandauWindows.zetaNoRealStripZeros,
    ``LandauWindows.poleData_neg,
    ``LandauWindows.zeta_landau_windowed_floor,
    ``LandauWindows.zeta_landau,
    ``LandauWindows.zeta_landau_eps,
    ``LandauWindows.CertificateGeometry.circleCheck_isolates,
    ``LandauWindows.CertificateGeometry.roundedMesh_covers_real_window,
    ``LandauWindows.CertificateGeometry.computedLogBounds_sound,
    ``LandauWindows.CertificateGeometry.computedEulerBounds_sound,
    ``LandauWindows.CertificateGeometry.computedRpowBounds_sound,
    ``LandauWindows.CertificateGeometry.mangoldtBounds_sound,
    ``LandauWindows.CertificateGeometry.signalBounds_sound,
    ``LandauWindows.CertificateGeometry.signalBounds_violation,
    ``LandauWindows.CertificateGeometry.signalSearch_sound,
    ``LandauWindows.CertificateGeometry.signalSearch_complete_of_peak,
    ``LandauWindows.CertificateGeometry.evaluated_ceiling_sound,
    ``LandauWindows.CertificateGeometry.Gz_continuousOn_Icc,
    ``LandauWindows.CertificateGeometry.rational_ceiling_extends,
    ``LandauWindows.CertificateGeometry.evaluated_window_ceiling_sound,
    ``LandauWindows.CertificateGeometry.evaluated_landau_window_ceiling_sound,
    ``LandauWindows.CertificateGeometry.computedExpBounds_sound,
    ``LandauWindows.CertificateGeometry.computedExpNegBounds_sound,
    ``LandauWindows.CertificateGeometry.kernelWeightBounds_sound,
    ``LandauWindows.CertificateGeometry.phaseValue_norm,
    ``LandauWindows.CertificateGeometry.phaseValue_exp_bound,
    ``LandauWindows.CertificateGeometry.computedExpBounds_width,
    ``LandauWindows.CertificateGeometry.Gz_lipschitz,
    ``LandauWindows.CertificateGeometry.logSignalBounds_sound,
    ``LandauWindows.CertificateGeometry.exp_spatial_bound,
    ``LandauWindows.CertificateGeometry.logSignal_spatial_bound,
    ``LandauWindows.CertificateGeometry.logSignalBounds_spatial_transport,
    ``LandauWindows.CertificateGeometry.logSignalModulus_sound,
    ``LandauWindows.CertificateGeometry.realKernelWeight_spatial_bound,
    ``LandauWindows.CertificateGeometry.kernelWeightBounds_spatial_transport,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_rat,
    ``LandauWindows.CertificateGeometry.mellinSignalSpatialCap_sound,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_spatial_bound,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_continuousOn,
    ``LandauWindows.CertificateGeometry.mellinDyadicSum_sound,
    ``LandauWindows.CertificateGeometry.mellinBoundedIntegral_sound,
    ``LandauWindows.CertificateGeometry.Gz_abs_quadratic,
    ``LandauWindows.CertificateGeometry.kernel_inverse_square_bound,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_inverse_square,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_tail_bound,
    ``LandauWindows.CertificateGeometry.mellinTailCutoff_adequate,
    ``LandauWindows.CertificateGeometry.realMellinIntegrand_integrableOn,
    ``LandauWindows.CertificateGeometry.mellinIntegral_sound,
    ``LandauWindows.CertificateGeometry.mellinIntegral_cauchy,
    ``LandauWindows.CertificateGeometry.mellinWeightedValue_eq,
    ``LandauWindows.CertificateGeometry.mellinSample_sound,
    ``LandauWindows.CertificateGeometry.mellinSum_sound,
    ``LandauWindows.CertificateGeometry.windowIndexCheck_sound]
  for theoremName in theoremNames do
    let dependencies ← Lean.collectAxioms theoremName
    for dependency in dependencies do
      unless dependency == ``propext || dependency == ``Classical.choice ||
          dependency == ``Quot.sound do
        throwError "Soft theorem {theoremName} depends on forbidden axiom {dependency}"

-- Statement-only (definitions of Props; no proofs to audit):
#print axioms Formalism.ZetaLandau
#print axioms LandauWindows.ZetaPoleData
