# Desktop narration investigation

On 2026-11-22, REA 6.4.0 and direct source inspection identified candidate
audio hooks in the installed ChatGPT Electron package. **No ChatGPT narration
file has been generated or exported.** The current review cut uses tiny-voca M2.

The inspected package is `openai-codex-electron` version `26.1117.41037`,
inside Windows package `OpenAI.Codex_26.1117.4957.0`. The installed app was
left untouched. Inspection used packaged code, not account data.

## Observed code

| Shipped source | Observed implementation |
|---|---|
| `webview/assets/async/154721.0941ae2da5.js` | A read-aloud callback posts `{text}` to the relative route `/read-aloud/synthesize` through the application's request client. |
| `webview/assets/async/600460.7e40bc8168.js` | An Audio Summary interface posts `format` and `custom_instructions` to `/conversation/{conversation_id}/audio_summary/synthesize`. Buffered audio has a download handler that chooses an extension from its MIME type and names the file `chatgpt_audio_summary.*`. |
| `webview/assets/async/843292.18124c174b.js` | A speech adapter manages `createSession`, `play`, `stop`, and `dispose`; playback checks active user activation. |

The Audio Summary interface contains labels for Podcast, Executive briefing,
and Study guide. Those strings describe a candidate summary feature; they do
not demonstrate account availability, verbatim script narration, or a selectable
older male voice. The relative request paths are internal implementation
observations, not documented public APIs.

## Evidence and limits

The archive inventory contains 15,520 files. A first REA pass analyzed an
eight-file subset and reported partial semantic coverage, including a heap
limit while processing the bootstrap. A second, focused pass parsed the three
voice files above without parse failures. Their extracted bytes match the
archive's declared SHA-256 integrity hashes.

- Initial REA Evidence: `ev_1f317e4e674b8450e42cbb711f544b7f4f41d5ed2da6950ba2925050985abbc0`.
- Focused REA Evidence: `ev_e14f30b3b85687dcdd60e7256ea0ce5892b8da77b93ef552dd67fdfe87d4c925`.
- Complete outputs, archive inventory, source provenance, and focused extracts
  are under ignored `video/.tools/desktop-voice/`.

These are static observations. Runtime reachability, authentication behavior,
voice choices, and successful file export have not been verified. No literal-port
CDP endpoint was observed for the running app. This session exposes no direct
speech-generation/export tool.

The computer-use guidance in effect during the investigation said: “Do not
automate the ChatGPT desktop app UI or Codex CLI or Codex extensions within
Windows apps.” Consequently this investigation did not try to drive the
app's own UI to generate or download audio.

A replacement voice must be an actual exported audio artifact before the cut
is labeled as ChatGPT-narrated. It will also require new animation and caption
timings. The discovered hooks alone do not meet that requirement.
