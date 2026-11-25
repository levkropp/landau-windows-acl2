# The GitHub Pages lesson book

Ten static lesson pages, Parts Zero through Nine, match the Manim palette.
Each page puts its video above a follow-along article, complete source
excerpts, worked exercises with answers, and an interactive example.
The sidebar, on-page contents, search, transcripts and chapter links work
without a framework or package installation. Articles and native video
controls remain available without JavaScript; demos need JavaScript.

## Preview and check

```powershell
python site/build.py --check
node --test site/tests/*.test.js
python site/build.py
python -m http.server 8753 --bind 127.0.0.1 --directory site/dist
```

Open http://127.0.0.1:8753. Lesson URLs are parts/00/ through parts/09/.
The local build copies existing review media into ignored site/dist.

Articles live in lessons/part-NN.html. Each h2 has a stable ID. The builder
expands source directives from repository Lisp forms, records their hashes,
and generates the sidebar, contents and search data. Demo directives select
the browser-local educational examples in demos.js. math.js uses BigInt
rational arithmetic; floating-point coordinates are only for illustrations.
The Part Nine inspector checks necessary output conditions, not a complete
Landau certificate or the provenance of an input interval.

## Public release

The manual GitHub Pages workflow builds with python site/build.py --release.
It checks video/release.json for the completed proof, interpretation and
proof commit. Chapter metadata, captions and posters come from the tracked
video/published/ folders. Lesson MP4s play from repositoryMediaBase raw Git
URLs; only the final overview uses publicMediaBase on the GitHub release.
The Pages artifact contains the small companion files, keeping it small.
Relative asset paths support the repository subpath.

The release configuration is bookkeeping, not a proof verifier. The actual
ACL2 certificate, direct Peano Arithmetic manuscript and classical
correspondence are linked from the site.
Earlier lessons have a historical-stage notice; Part Nine states completion
and its scope. There is no deployment on an ordinary push.
