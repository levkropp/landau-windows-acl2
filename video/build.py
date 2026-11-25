"""Build the local review draft, subtitles, and chapter metadata."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
import subprocess
import textwrap
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def ensure_reference():
    pin = json.loads((ROOT / "reference.json").read_text(encoding="utf8"))
    destination = ROOT / ".tools/reference"
    destination.mkdir(parents=True, exist_ok=True)
    for filename, expected in pin["files"].items():
        path = destination / filename
        if not path.exists():
            url = f"https://raw.githubusercontent.com/harttraveller/riemann/{pin['revision']}/video/{filename}"
            urllib.request.urlretrieve(url, path)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Reference asset {filename} differs from the pinned revision.")


def timestamp(seconds: float, vtt=False):
    milliseconds = round(seconds * 1000)
    hours, milliseconds = divmod(milliseconds, 3_600_000)
    minutes, milliseconds = divmod(milliseconds, 60_000)
    seconds, milliseconds = divmod(milliseconds, 1000)
    return f"{hours:02}:{minutes:02}:{seconds:02}{'.' if vtt else ','}{milliseconds:03}"


def validate_movie(path, cues):
    info = json.loads(subprocess.check_output([
        "ffprobe", "-v", "error", "-show_entries",
        "format=duration:stream=codec_type,codec_name,width,height,r_frame_rate,duration",
        "-of", "json", str(path)], text=True))
    kinds = {stream["codec_type"] for stream in info["streams"]}
    if not {"video", "audio", "subtitle"}.issubset(kinds):
        raise ValueError("The packaged video is missing a required stream.")
    duration = float(info["format"]["duration"])
    previous = 0
    for start, end, _ in cues:
        if not previous <= start < end <= duration:
            raise ValueError("A caption is out of sequence or outside the finished movie.")
        previous = end
    audio = next(s for s in info["streams"] if s["codec_type"] == "audio")
    if float(audio["duration"]) < previous - 0.1:
        raise ValueError("The audio ends before the final spoken caption.")
    decoded = subprocess.run([
        "ffmpeg", "-v", "error", "-i", str(path), "-map", "0:v:0", "-map", "0:a:0",
        "-fps_mode", "passthrough", "-enc_time_base", "demux", "-f", "null", os.devnull],
        capture_output=True, text=True, check=True)
    if decoded.stderr.strip():
        raise ValueError(f"Full movie decode reported errors: {decoded.stderr}")
    info["full_decode"] = "passed"
    info["caption_and_audio_bounds"] = "passed"
    return info


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--draft", choices=["01", "02", "03", "04", "05"], default="05")
    parser.add_argument("--episode", choices=["00", "01", "02", "03", "04", "05", "06", "07", "08", "09"], help="Build a series episode instead of the overview")
    parser.add_argument("--preview", action="store_true", help="Render at 720p instead of 1080p")
    parser.add_argument("--skip-render", action="store_true", help="Only refresh captions/chapters")
    parser.add_argument("--append-reference", action="store_true",
                        help="Also append the 1080p draft to the locally downloaded reference")
    args = parser.parse_args()
    variants = {
        "01": ("narration.json", "manifest.json", "followup.py", "LandauFollowup", "timing.json"),
        "02": ("narration-v2.json", "manifest-v2.json", "repo_story.py", "LandauRepoStory", "timing-v2.json"),
        "03": ("narration-v3.json", "manifest-v3.json", "foundations_story.py", "LandauFoundationsStory", "timing-v3.json"),
        "04": ("narration-v4.json", "manifest-v4.json", "revision_four.py", "LandauRevisionFour", "timing-v4.json"),
        "05": ("narration-v5.json", "manifest-v5.json", "revision_five.py", "LandauRevisionFive", "timing-v5.json"),
    }
    narration, manifest, scene_file, scene_name, timing_file = variants[args.draft]
    stem = "landau-windows-acl2-overview-05" if args.draft == "05" else f"{'landau-windows-acl2' if args.draft in ('03', '04') else 'landau-windows'}-draft-{args.draft}"
    episodes = {
        "00": ("narration-part00.json", "manifest-part00.json", "part_zero.py", "PartZero",
               "timing-part00-r6.json", "landau-windows-acl2-part-00-r6"),
        "01": ("narration-part01.json", "manifest-part01.json", "part_one.py", "PartOne",
               "timing-part01-r3.json", "landau-windows-acl2-part-01-r3"),
        "02": ("narration-part02.json", "manifest-part02.json", "part_two.py", "PartTwo",
               "timing-part02.json", "landau-windows-acl2-part-02"),
        "03": ("narration-part03.json", "manifest-part03.json", "part_three.py", "PartThree",
               "timing-part03.json", "landau-windows-acl2-part-03"),
        "04": ("narration-part04.json", "manifest-part04.json", "part_four.py", "PartFour",
               "timing-part04.json", "landau-windows-acl2-part-04"),
        "05": ("narration-part05.json", "manifest-part05.json", "part_five.py", "PartFive",
               "timing-part05.json", "landau-windows-acl2-part-05"),
        "06": ("narration-part06.json", "manifest-part06.json", "part_six.py", "PartSix",
               "timing-part06.json", "landau-windows-acl2-part-06"),
        "07": ("narration-part07.json", "manifest-part07.json", "part_seven.py", "PartSeven",
               "timing-part07.json", "landau-windows-acl2-part-07"),
        "08": ("narration-part08.json", "manifest-part08.json", "part_eight.py", "PartEight",
               "timing-part08.json", "landau-windows-acl2-part-08"),
        "09": ("narration-part09.json", "manifest-part09.json", "part_nine.py", "PartNine",
               "timing-part09.json", "landau-windows-acl2-part-09"),
    }
    if args.episode:
        narration, manifest, scene_file, scene_name, timing_file, stem = episodes[args.episode]
    if args.episode or args.draft != "01":
        ensure_reference()
    if args.episode == "04":
        subprocess.run([sys.executable,str(ROOT / "prepare_part_four.py")],check=True,cwd=ROOT)
    if args.episode == "05":
        subprocess.run([sys.executable,str(ROOT / "prepare_part_five.py")],check=True,cwd=ROOT)
    if args.episode == "06":
        subprocess.run([sys.executable,str(ROOT / "prepare_part_six.py")],check=True,cwd=ROOT)
    if args.episode == "07":
        subprocess.run([sys.executable,str(ROOT / "prepare_part_seven.py")],check=True,cwd=ROOT)
    if args.episode == "08":
        subprocess.run([sys.executable,str(ROOT / "prepare_part_eight.py")],check=True,cwd=ROOT)
    if args.episode == "09" or (not args.episode and args.draft == "05"):
        subprocess.run([sys.executable,str(ROOT / "prepare_part_nine.py")],check=True,cwd=ROOT)
    subprocess.run(["node", str(ROOT / "synthesize.mjs"), narration, manifest], check=True, cwd=ROOT)
    resolution = "720p30" if args.preview else "1080p30"
    source = ROOT / f"media/videos/{Path(scene_file).stem}/{resolution}/{stem}.mp4"
    if not args.skip_render:
        scratch = ROOT / ".tools/renders" / stem
        subprocess.run([sys.executable, "-m", "manim", "render", str(ROOT / scene_file),
                        scene_name, "--media_dir", str(scratch),
                        "-r", "1280,720" if args.preview else "1920,1080", "--fps", "30",
                        "--format", "mp4", "--output_file", stem,
                        "--disable_caching"], check=True, cwd=ROOT)
        source.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(scratch / f"videos/{Path(scene_file).stem}/{resolution}/{stem}.mp4", source)
    timings = json.loads((ROOT / "media" / timing_file).read_text(encoding="utf8"))
    cues = []
    for segment in timings:
        for sentence in segment["sentences"]:
            # Display conventional spellings while synthesizing acronyms explicitly.
            text = sentence["text"].replace("Landau Windows A C L two", "Landau Windows ACL Two")
            text = text.replace("A C L two", "ACL2").replace("Z F C", "ZFC").replace("Godel", "Gödel")
            cues.append((segment["audio_start"] + sentence["start"],
                         segment["audio_start"] + sentence["end"], text))
    srt = []
    vtt = ["WEBVTT\n"]
    for index, (start, end, text) in enumerate(cues, 1):
        lines = "\n".join(textwrap.wrap(text, width=68))
        srt.append(f"{index}\n{timestamp(start)} --> {timestamp(end)}\n{lines}\n")
        vtt.append(f"{timestamp(start, True)} --> {timestamp(end, True)}\n{lines}\n")
    (ROOT / f"media/{stem}.srt").write_text("\n".join(srt), encoding="utf8")
    (ROOT / f"media/{stem}.vtt").write_text("\n".join(vtt), encoding="utf8")
    chapters = [f"{timestamp(s['start'], True)[:-4]}  {s['chapter']}" for s in timings]
    (ROOT / f"media/{stem}-chapters.txt").write_text("\n".join(chapters) + "\n", encoding="utf8")
    transcript = []
    for segment in timings:
        transcript.append(f"## {timestamp(segment['start'], True)[:-4]} — {segment['chapter'].replace('Godel', 'Gödel')}\n")
        words = " ".join(s["text"] for s in segment["sentences"])
        words = words.replace("Landau Windows A C L two", "Landau Windows ACL Two")
        transcript.append(words.replace("A C L two", "ACL2").replace("Z F C", "ZFC").replace("Godel", "Gödel") + "\n")
    (ROOT / f"media/{stem}-transcript.md").write_text("\n".join(transcript), encoding="utf8")
    output = ROOT / f"media/{stem}{'-preview' if args.preview else ''}.mp4"
    building = output.with_name(output.stem + ".building.mp4")
    title = json.loads((ROOT / narration).read_text(encoding="utf8"))["title"]
    review = json.loads((ROOT / narration).read_text(encoding="utf8")).get("version", "Review")
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-i", str(source), "-i",
                    str(ROOT / f"media/{stem}.srt"),
                    "-map", "0:v:0", "-map", "0:a:0", "-map", "1:0",
                    "-c:v", "copy", "-c:a", "aac", "-b:a", "160k", "-ar", "48000",
                    "-af", "loudnorm=I=-16:TP=-1.5:LRA=11", "-c:s", "mov_text",
                    "-metadata", f"title=landau-windows-acl2 - {title} - {review}",
                    "-metadata:s:s:0", "language=eng", "-movflags", "+faststart", str(building)], check=True)
    verification = validate_movie(building, cues)
    building.replace(output)
    verification["published_file"] = str(output)
    (ROOT / f"media/{stem}-verification.json").write_text(json.dumps(verification, indent=2), encoding="utf8")
    web = {"title": title, "chapters": []}
    for segment in timings:
        words = " ".join(s["text"] for s in segment["sentences"])
        words = words.replace("Landau Windows A C L two", "Landau Windows ACL Two")
        web["chapters"].append({"start": segment["start"], "chapter": segment["chapter"].replace("Godel", "Gödel"),
                                "text": words.replace("A C L two", "ACL2").replace("Z F C", "ZFC").replace("Godel", "Gödel")})
    (ROOT / f"media/{stem}-web.json").write_text(json.dumps(web, ensure_ascii=False, indent=2), encoding="utf8")
    poster_spec = json.loads((ROOT / narration).read_text(encoding="utf8")).get("poster")
    poster_time = 18
    if poster_spec:
        segment = next(s for s in timings if s["id"] == poster_spec["segment"])
        poster_time = segment["audio_start"] + segment["sentences"][poster_spec["cue"]]["start"] + poster_spec.get("offset", 0)
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-ss", str(poster_time), "-i", str(output), "-frames:v", "1",
                    "-vf", "scale=1440:-1", str(ROOT / f"media/{stem}-poster.jpg")], check=True)
    if args.append_reference:
        if args.preview:
            raise ValueError("Appending requires the 1080p render to match the reference.")
        reference = ROOT / ".tools/reference/full.mp4"
        if not reference.exists():
            raise FileNotFoundError("Download the README's reference to video/.tools/reference/full.mp4 first.")
        listing = ROOT / "media/append-list.txt"
        listing.write_text("\n".join(f"file '{p.as_posix()}'" for p in (reference, output)) + "\n", encoding="utf8")
        combined = ROOT / f"media/riemann-with-landau-draft-{args.draft}.mp4"
        subprocess.run(["ffmpeg", "-v", "error", "-y", "-f", "concat", "-safe", "0", "-i", str(listing),
                        "-map", "0:v:0", "-map", "0:a:0", "-c:v", "copy", "-c:a", "aac", "-b:a", "160k",
                        "-af", "aresample=async=1:first_pts=0", "-ar", "48000",
                        "-movflags", "+faststart", str(combined)], check=True)
        print(f"Reference plus follow-up: {combined}")
    print(f"Review video: {output}")
    print("Captions and chapters written under video/media/")


if __name__ == "__main__":
    main()
