# Narration without API keys

The preferred workflow is local and requires no API keys. The active build
uses tiny-voca M2. No hosted speech request is part of it.

The [Desktop investigation](DESKTOP-VOICE.md) found packaged read-aloud
synthesis and Audio Summary download code using REA. These static findings
have not produced an exported narration file. This session has no direct
speech-generation/export tool, and its computer-use instructions exclude
driving ChatGPT's own UI. Keep the review voice labeled M2 until replacement
audio exists. The [official Voice guide](https://help.openai.com/en/articles/20001274-chatgpt-voice)
describes conversational Voice; it is separate from the static findings.

The earlier API audition scaffold has been removed. Voice quality can be
revisited if a suitable local or directly supported export option becomes
available. A different voice will need matching animation and caption timing.

For local teaching scripts, keep standard spelling in `text` and use
`spoken_text` for what the synthesizer should pronounce. Prefer variables
`x` and `y`, spoken as “ex” and “why”; read comparisons out in words. The two versions
must have matching sentence counts. Ellipses in `spoken_text` insert silence
instead of relying on the synthesizer's punctuation handling. The sentence
and phrase timings follow any playback-rate adjustment, so animations can
wait for the relevant phrase. Captions retain the conventional letters.
Always say “Peano Arithmetic” in narration, even when the screen or captions
use “PA”. The synthesizer expands this abbreviation before hashing and
generating speech so cached audio matches the spoken wording.
