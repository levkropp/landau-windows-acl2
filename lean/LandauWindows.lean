/-
Landau Windows — the Lean formalization (Phase 2).

Soft layer (this entry point):
  * `Formalism.Sz`, `Formalism.Gz`, `Formalism.ZetaLandau` — the
    statements, lifted verbatim from the Alpöge archive for
    line-by-line comparability (`LandauWindows/Statement.lean`);
  * `LandauWindows.Soft.*` — the abstract windowed-Landau cluster,
    lifted from the archive with provenance headers, culminating in
    `Deduction.landau_window`;
  * `LandauWindows.zeta_landau_windowed` — the ζ-facing windowed
    Landau theorem (ours): `ZetaPoleData` (the analytic content,
    hypothesis-injected) plus ceilings on recurring windows
    `[Y, Y ^ (3/2)]` exclude zeros with real part > θ.

The effective shadow in `LandauWindows/Shadow/` proves scaled-integer interval
and mesh-search lemmas with explicit witnesses and no choice dependencies.
The full effective analytic reduction remains in progress; see ../docs/roadmap.md.
-/
import LandauWindows.Statement
import LandauWindows.Soft.ZetaWindowed
import LandauWindows.Soft.MellinRamp
import LandauWindows.Soft.ZetaPoleData
import LandauWindows.Soft.ZeroFreeOfRpowWindow
import LandauWindows.Soft.ZetaReal
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
import LandauWindows.Axioms
import LandauWindows.Shadow.Axioms
