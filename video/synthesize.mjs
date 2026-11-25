// Local, deterministic narration using the already pinned tiny-voca runtime.
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { readGGUF, TinyVoca } from "./.tools/tiny-voca/js/tiny-voca.js";
import { fromGGUF } from "./.tools/tiny-voca/js/dizione/engine.js";
import { utterancesOf, limited, wav } from "./.tools/tiny-voca/js/text.js";

const root = dirname(fileURLToPath(import.meta.url));
const script = JSON.parse(readFileSync(join(root, process.argv[2] ?? "narration.json"), "utf8"));
const audioDir = join(root, "audio");
mkdirSync(audioDir, { recursive: true });
const bytes = readFileSync(join(root, ".tools/tiny-voca/js/tiny-voca.gguf"));
const file = readGGUF(bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength));
const voca = new TinyVoca(file);
const phonemizer = await fromGGUF(file);
const rate = voca.config.sample_rate;
const manifest = { title: script.title, voice: script.voice, sample_rate: rate, segments: [] };

// Ellipses are deliberate teaching pauses, not sentence boundaries. Keep
// phonetic speech separate from the conventional text used by captions.
const pauseMarker = "\uE000";
function sentencesOf(text) {
  return (text.replace(/\.{3,}|…/g, pauseMarker).match(/[^.!?]+(?:[.!?]+|$)/g) ?? [])
    .map(s => s.trim()).filter(Boolean);
}

for (const segment of script.segments) {
  // Keep the abbreviation in captions, but always speak the full name.
  const spokenText = (segment.spoken_text ?? segment.text)
    .replace(/\bP[ \t]+A\b|\bPA\b/g, "Peano Arithmetic");
  if (spokenText !== (segment.spoken_text ?? segment.text)) segment.spoken_text = spokenText;
  const advanced = Boolean(segment.spoken_text || /\.{3,}|…/.test(segment.text));
  const cacheInput = {
    text: segment.text, voice: script.voice, weights: "8436ad1c9b57c3533c925588a1b3563f906079a89c081ac0bec9f31ad6e28653",
    format: advanced ? 2 : 1, rate: segment.rate ?? 1,
  };
  if (advanced) Object.assign(cacheInput, { spoken_text: segment.spoken_text ?? segment.text,
    ellipsis_pause: segment.ellipsis_pause ?? 0.48, sentence_pause: segment.sentence_pause ?? 0.36 });
  const hash = createHash("sha256").update(JSON.stringify(cacheInput)).digest("hex").slice(0, 16);
  const stem = `${segment.id}-${hash}`;
  const output = join(audioDir, `${stem}.wav`);
  const metadata = join(audioDir, `${stem}.json`);
  let timings;
  if (existsSync(output) && existsSync(metadata)) {
    timings = JSON.parse(readFileSync(metadata, "utf8"));
  } else {
    const chunks = [];
    const sentences = sentencesOf(segment.text);
    const spoken = sentencesOf(segment.spoken_text ?? segment.text);
    if (sentences.length !== spoken.length) throw new Error(`${segment.id}: display/speech sentence counts differ`);
    let samples = 0;
    timings = { sentences: [] };
    for (const [sentenceIndex, raw] of sentences.entries()) {
      const text = raw.replaceAll(pauseMarker, "…");
      const start = samples / rate;
      const phrases = [];
      for (const [phraseIndex, phrase] of spoken[sentenceIndex].split(pauseMarker).entries()) {
        if (phraseIndex) {
          const pause = new Float32Array(Math.round(rate * (segment.ellipsis_pause ?? 0.48)));
          chunks.push(pause); samples += pause.length;
        }
        const phraseStart = samples / rate;
        const utterances = utterancesOf(phrase.trim(), phonemizer, voca.config.max_tokens - 12);
        for (const [utteranceIndex, utterance] of utterances.entries()) {
          const { audio } = voca.synthesize(utterance.ids, utterance.stress, {
            voice: script.voice, seed: sentenceIndex * 100 + phraseIndex * 10 + utteranceIndex,
          });
          chunks.push(audio); samples += audio.length;
        }
        phrases.push({ start: phraseStart, end: samples / rate });
      }
      timings.sentences.push({ text, start, end: samples / rate, phrases });
      const pause = new Float32Array(Math.round(rate * (advanced ? (segment.sentence_pause ?? 0.36) : 0.24)));
      chunks.push(pause);
      samples += pause.length;
    }
    const whole = new Float32Array(samples);
    let offset = 0;
    for (const chunk of chunks) { whole.set(chunk, offset); offset += chunk.length; }
    const speechRate = segment.rate ?? 1;
    const rawPath = speechRate === 1 ? output : join(audioDir, `${stem}-unpaced.wav`);
    writeFileSync(rawPath, new Uint8Array(wav(limited(whole), rate)));
    if (speechRate !== 1) {
      execFileSync("ffmpeg", ["-v", "error", "-y", "-i", rawPath, "-af", `atempo=${speechRate}`, output]);
      for (const sentence of timings.sentences) {
        sentence.start /= speechRate;
        sentence.end /= speechRate;
        for (const phrase of sentence.phrases) {
          phrase.start /= speechRate; phrase.end /= speechRate;
        }
      }
    }
    timings.duration = Number(execFileSync("ffprobe", ["-v", "error", "-show_entries", "format=duration",
      "-of", "default=nw=1:nk=1", output], { encoding: "utf8" }).trim());
    writeFileSync(metadata, JSON.stringify(timings, null, 2));
  }
  manifest.segments.push({ ...segment, audio: `audio/${stem}.wav`, ...timings });
  console.log(`${segment.id}: ${timings.duration.toFixed(2)} s, ${script.voice}`);
}
writeFileSync(join(audioDir, process.argv[3] ?? "manifest.json"), JSON.stringify(manifest, null, 2));
