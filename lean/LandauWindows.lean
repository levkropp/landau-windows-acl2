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

The effective shadow (choice-free, witness-explicit, ℚ-intervals) lives
in `LandauWindows/Shadow/` as Phase 2 proceeds; see ../docs/roadmap.md.
-/
import LandauWindows.Statement
import LandauWindows.Soft.ZetaWindowed
import LandauWindows.Axioms
