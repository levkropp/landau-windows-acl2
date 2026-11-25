# Completed media release

Proof checkpoint: 52aec9e915b5d816ff23a66b942500684643f8f6.
The theorem is lw-euler-window-encoded-zero-reduction; its arithmetic and
classical interpretation is docs/acl2-interpretation.md.

The completion audit records 647 fresh book certificates, 3,649 exported
theorems, successful import of the final 558-book closure, and the recorded
347-definition natural-measure audit. The encoded windowed ceiling
reduction is proved directly in first-order Peano Arithmetic in
classical/pa-paper.pdf, Theorem 15.2, with the corresponding development
certified in vanilla ACL2. The manuscript also supplies the classical
zeta correspondence. A full RH proof in arithmetic is a further question.

Revision five is the final overview; Part Nine completes the lesson series.
Older films retain the progress language appropriate to their recording.
The README feature links the final overview and the GitHub Pages lesson
book. The first public media tag is v1.0.0.

Release procedure:

1. Render both final films and validate complete decoding, captions and
   audio bounds; inspect the actual rendered frames and ending.
2. Run package_release.py. It copies the ten lesson MP4s and all companion
   files into tracked video/published/ folders and stages only the final
   overview MP4 under ignored .tools/release-overview-v1.0.0/. The PA paper
   remains in classical/. Sizes and SHA-256 hashes are recorded separately
   for repository files and the single release asset in release-assets.json.
3. Commit and push the source, lesson videos, companion files, README and
   release configuration. Verify that the lesson raw URLs serve MP4 data.
4. Keep only the final overview MP4 attached to the GitHub release. The
   captions, chapter data, transcripts, posters, audit files and PA paper
   are available from the repository rather than duplicated as attachments.
5. Build the public lesson book using the tracked companion files and raw
   lesson MP4 URLs, deploy GitHub
   Pages through the manual workflow, and verify the returned public URLs.

Release bookkeeping is not a replacement for the theorem audit. The
narration uses local tiny-voca M2 without API keys.
