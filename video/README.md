# Video course and completed overview

[Watch the final overview](https://github.com/levkropp/landau-windows-acl2/releases/download/v1.0.0/landau-windows-acl2-overview-05.mp4) · [Lesson book](https://levkropp.github.io/landau-windows-acl2/) · [Release media](https://github.com/levkropp/landau-windows-acl2/releases/tag/v1.0.0)

Revision five reports the encoded windowed Landau ceiling reduction,
proved in first-order Peano Arithmetic and certified in vanilla ACL2.
The [PA manuscript](../classical/pa-paper.pdf) gives the direct arithmetic
proof in Theorem 15.2 and supplies the classical zeta correspondence.
This is the Landau conversion under its stated hypotheses; a full RH proof
in arithmetic is a further question.
[Overview source notes](SOURCES-v5.md) · [Interpretation](../docs/acl2-interpretation.md)

## The series

| Part | Lesson | Source and scope |
| --- | --- | --- |
| 00 | Successor, recursive arithmetic and induction | [Teaching book](teaching-examples.lisp) |
| 01 | Proofs, models and stronger foundations | [Notes](SOURCES-part01.md) |
| 02 | Exact rational intervals and error budgets | [Notes](SOURCES-part02.md) |
| 03 | Finite search, coverage and transported margins | [Notes](SOURCES-part03.md) |
| 04 | Prime powers and the centered signal | [Notes](SOURCES-part04.md) |
| 05 | The classical one-sided Landau bridge | [Notes](SOURCES-part05.md) |
| 06 | Scalar kernels, meshes and tail budgets | [Notes](SOURCES-part06.md) |
| 07 | Rational phases and oscillating samples | [Notes](SOURCES-part07.md) |
| 08 | Checked geometry and the conditional coefficient chain | [Notes](SOURCES-part08.md) |
| 09 | Generated contours and the completed arithmetic reduction | [Notes](SOURCES-part09.md) |

Earlier films preserve their historical progress statements. Part Nine
explains the obligations subsequently discharged. The companion site puts
each video above a worked article, source excerpts and an educational demo.
The demos do not run ACL2 or replace its certificates.

## Rebuild locally

The existing virtual environment uses Manim Community 0.22.1 and the pinned
reference assets in [reference.json](reference.json). Narration uses the
local tiny-voca male M2 voice, with no API keys or hosted speech service.
See [setup.ps1](setup.ps1) and [NARRATION.md](NARRATION.md).

```powershell
.\\video\\.venv\\Scripts\\python.exe video/build.py --draft 05
.\\video\\.venv\\Scripts\\python.exe video/build.py --episode 09
```

All episode IDs 00 through 09 are accepted. The default is the completed
overview. Use --preview for 720p or --skip-render to repackage an existing
render. Revision four remains reproducible with --draft 04.

Builds write temporary frames, glyphs and segments under ignored
video/.tools/renders, and only current full render inputs under
video/media/videos. Finished MP4s are replaced atomically after packaging,
full-file decoding and caption/audio-bound checks. Captions, chapter lists,
transcripts, posters and web metadata use the same sentence timings.

Part Nine and revision five audit the completed proof and freeze the source
shown on screen; they import the final certificate closure without claiming
a fresh full recertification during rendering. Earlier preparation scripts
keep their independent teaching certificates separate from project counts.

The ten lesson MP4s are ordinary Git files under [published/](published/README.md),
with direct raw URLs. Captions, posters, transcripts and timings live beside
each lesson. The final overview MP4 is the only attached GitHub release asset.
The [media manifest](release-assets.json) records repository and release
file sizes and SHA-256 hashes. See [the release record](RELEASE.md),
[series teaching rules](SERIES.md), and [site build instructions](../site/README.md).
