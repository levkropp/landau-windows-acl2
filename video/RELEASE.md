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
2. Package the ten current lessons and overview with captions, posters,
   transcripts, chapter metadata, portable verification records and the
   PA manuscript PDF and TeX source. Record
   sizes and SHA-256 hashes in release-assets.json.
3. Commit the source, lesson book, README and release configuration after
   the separate proof checkpoint, then push both commits.
4. Upload all media to a draft GitHub release at that source commit, verify
   its asset inventory and sizes, then publish the release.
5. Build the public lesson book from the published media, deploy GitHub
   Pages through the manual workflow, and verify the returned public URLs.

Release bookkeeping is not a replacement for the theorem audit. The
narration uses local tiny-voca M2 without API keys.
