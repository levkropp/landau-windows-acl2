# From arithmetic to the Landau bridge

Audience: undergraduate discrete mathematics, explained through worked
examples and visual arguments. Introduce a construction before using it.

## Current episodes

- [Part Zero](media/landau-windows-acl2-part-00-r6.mp4): the language of
  Peano Arithmetic, successor chains, recursive calculation, and induction.
  Worked proofs of `0 + n = n` and the odd-number square identity lead to
  ACL2 statements. Its [teaching book](teaching-examples.lisp) certifies six theorems.
- [Part One](media/landau-windows-acl2-part-01-r3.mp4): proof steps, models,
  consistency, Gödel's second theorem, and stronger backgrounds. Code popups
  introduce the clock and digit encoder. Its [six teaching theorems](teaching-part01.lisp)
  do not include a consistency proof or a full Peano Arithmetic proof checker.
  See the [source and scope notes](SOURCES-part01.md).
- [Part Two](media/landau-windows-acl2-part-02.mp4): exact fractions,
  interval representations, addition, subtraction, scaling, widths, error
  radii, and precision budgets. Positive lower endpoints and strict margins
  lead toward finite search. Its [teaching book](teaching-part02.lisp)
  copies the project's five interval definitions and certifies eight theorems.
  The [source notes](SOURCES-part02.md) distinguish rational certificates
  from their real interpretation.
- [Part Three](media/landau-windows-acl2-part-03.mp4): a finite scan,
  returned indices and grid addresses, coverage, lower transport, and a
  conditional theorem forcing success. One numerical example links every
  stage. Its [teaching book](teaching-part03.lisp) certifies 18 theorems;
  the [source notes](SOURCES-part03.md) state the hypotheses and scope.
- [Part Four](media/landau-windows-acl2-part-04.mp4): prime-power certificates,
  rational logarithm bounds, weighted ramps, and the centering correction.
  Twenty functions are shown from certified project snapshots. Nine
  dependency books and [six additional teaching theorems](teaching-part04.lisp)
  certify independently; the [source notes](SOURCES-part04.md) distinguish
  arithmetic guarantees from real interpretation.
- [Part Five](media/landau-windows-acl2-part-05.mp4): the complex-plane map,
  recurring-window quantifiers, the classical ceiling-to-zero-free theorem,
  one-sided readings, and competing geometric scales. Four project dependency
  books plus [six teaching theorems](teaching-part05.lisp) certify in an
  isolated tree; the [source notes](SOURCES-part05.md) distinguish the
  analytic theorem from its finite arithmetic illustrations.
- [Part Six](media/landau-windows-acl2-part-06.mp4): rational exponential
  bands, decay bands, composed scalar kernel weights, and the distinction
  between exact finite sums and integral error. Seventeen functions are
  shown from source; eight project books plus [ten teaching theorems](teaching-part06.lisp)
  certify in isolation. See the [source notes](SOURCES-part06.md).

- [Part Seven](media/landau-windows-acl2-part-07.mp4): complex rational
  pairs, unit rotations, phase precision, log-signal transport, and three
  component error budgets. Thirty-six definitions lead to the actual
  oscillating sample and finite sum. Twenty-five project dependency books
  plus [ten teaching theorems](teaching-part07.lisp) certify in isolation.
  The [source notes](SOURCES-part07.md) distinguish rational evaluation
  from real interpretation, mesh coverage, tails and pole arguments.
- [Part Eight](media/landau-windows-acl2-part-08.mp4): reciprocal poles and
  coefficient scales, rational height selection, circle checks against
  boxes, complete-cover hypotheses, and model comparison. Ninety-three
  project books plus [twelve teaching theorems](teaching-part08.lisp)
  certify in isolation. The [source notes](SOURCES-part08.md) distinguish
  the conditional returned witness from the remaining general reduction.

- [Part Nine](media/landau-windows-acl2-part-09.mp4): the completed encoded-zero
  reduction, generated contours, quantifier order, returned rational witness,
  the direct Peano Arithmetic proof, and the classical correspondence. See the
  [source notes](SOURCES-part09.md).

The [series manifest](series.json) records the ten completed lessons. Teaching
results remain separate from the Landau project count. Revision five is the
final overview. Earlier films preserve the progress language from their
recording; Part Nine explains what subsequently closed those obligations.

## Teaching rules

- Always say “Peano Arithmetic” in narration, even when the screen uses
  “PA”. Prefer `x` and `y` to easily mispronounced isolated letters.
- State the domain and explain new notation. Read comparisons in words.
  Use `spoken_text` for pronunciation and ellipses for real pauses;
  conventional spellings remain in captions.
- Build examples before introducing abstraction. A predicate letter in
  induction is a formula template, not quantification over arbitrary sets.
- Show the ACL2 counterpart of each new arithmetic construction. Explain
  inputs and unfamiliar primitives before relying on them.
- Before using a new custom function compactly, show its complete definition
  from the checked source in a popup. Explain branches, boundary cases and
  recursive progress, then fold the card into a call badge. Long definitions
  need several readable panels. `function_popup.py` extracts the source forms.
  `lesson_source.py` supplies numbered source pages for longer forms.
- Use small footnotes for incidental details: the clock's `nfix` note says
  it preserves a natural number and returns zero for anything else.
- Distinguish width from error radius, an example from a general theorem,
  and an arithmetic certificate from its mathematical interpretation.
  Show every hypothesis needed by the displayed guarantee.
- Label schematic illustrations and unimplemented specifications. Do not
  present a specification as an executable, defined function.
- Keep narration independent of live theorem counts. The local site reads
  evidence from the proof ledger. The final overview and public site follow
  the completed proof milestone and [release checklist](RELEASE.md).

## Build and maintain

```powershell
.\video\.venv\Scripts\python.exe video/build.py --episode 00
.\video\.venv\Scripts\python.exe video/build.py --episode 01
.\video\.venv\Scripts\python.exe video/build.py --episode 02
.\video\.venv\Scripts\python.exe video/build.py --episode 03
.\video\.venv\Scripts\python.exe video/build.py --episode 04
.\video\.venv\Scripts\python.exe video/build.py --episode 05
.\video\.venv\Scripts\python.exe video/build.py --episode 06
.\video\.venv\Scripts\python.exe video/build.py --episode 07
.\video\.venv\Scripts\python.exe video/build.py --episode 08
.\video\.venv\Scripts\python.exe video/build.py --episode 09
```

Each episode has one current scene and narration file: `part_zero.py`,
`part_one.py`, `part_two.py`, `part_three.py`, `part_four.py`, `part_five.py`,
`part_six.py`, `part_seven.py`, `part_eight.py`, `part_nine.py`, and
`narration-partNN.json`.
`lesson_scene.py` supplies shared layout and phrase timing. The accepted
Part Zero and Part One lesson bodies were consolidated; their finished
review cuts retain their existing paths. Superseded media and caches are
in the ignored archive `video/.tools/archive/episodes-before-part02/`.
Its move manifest is `video/.tools/archive-episodes-plan.json`.
The later media-wide cleanup is under `.tools/archive/media-before-part03/`,
with move record `.tools/archive-media-part03.json`. Builds now keep all
temporary Manim files under `.tools/renders/`, leaving `media/videos/`
with only current full render inputs.
Part Four's build runs `prepare_part_four.py` to certify an isolated copy of
the actual evaluator dependencies. It reuses certificates only while their
source fingerprint is unchanged.
Part Five uses `prepare_part_five.py` for the same isolated ACL2 workflow
and also freezes the Lean source statement displayed in the film.
Part Six uses `prepare_part_six.py` for its kernel snapshots and certificates,
and records the two Lean interpretation sources separately.
Part Seven uses `prepare_part_seven.py` to certify the dependencies through
`mellin-quadrature` and its teaching book, and freezes three Lean bridge
sources without recertifying Lean. Full source cards use the same certified
snapshot; final video validation precedes replacement of the review MP4.
Part Eight uses `prepare_part_eight.py` for isolated certification of
`box-circles`, `mellin-window-budget`, their dependency closure and its
teaching book. It freezes the Lean geometry source separately. The final
reduction episode follows the completed proof checkpoint. Part Nine uses
`prepare_part_nine.py` to audit source freshness, import the final certificate
closure and freeze the source shown on screen, without claiming a fresh
recertification of every book during the media build.

The palette and font adapter build on the credited reference repository.
Part Zero also draws on Timothy Chow's
[The Consistency of Arithmetic](https://timothychow.net/consistent.pdf).
All new teaching scenes are original.
