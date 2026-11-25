"""Stage portable current media and record a SHA-256 release inventory."""
from __future__ import annotations
import hashlib,json,shutil
from pathlib import Path

ROOT=Path(__file__).resolve().parent
STAGE=ROOT/'.tools/release-v1.0.0'


def main():
    release=json.loads((ROOT/'release.json').read_text(encoding='utf8'))
    episodes=json.loads((ROOT/'series.json').read_text(encoding='utf8'))['episodes']
    entries=[(ep['id'],Path(ep['asset']).stem,ep['timing']) for ep in episodes]
    entries.append(('overview',Path(release['finalOverviewAsset']).stem,'timing-v5.json'))
    STAGE.mkdir(parents=True,exist_ok=True);assets=[]
    def record(target):
        with target.open('rb') as stream:digest=hashlib.file_digest(stream,'sha256').hexdigest()
        assets.append({'file':target.name,'bytes':target.stat().st_size,'sha256':digest})
    for identity,stem,timing in entries:
        verification=json.loads((ROOT/'media'/f'{stem}-verification.json').read_text(encoding='utf8'))
        if verification.get('full_decode')!='passed' or verification.get('caption_and_audio_bounds')!='passed':raise RuntimeError('Unverified movie: '+stem)
        for suffix in ['.mp4','.vtt','.srt','-poster.jpg','-web.json','-transcript.md','-chapters.txt','-verification.json']:
            source=ROOT/'media'/(stem+suffix);target=STAGE/source.name
            if suffix=='-verification.json':
                portable={k:v for k,v in verification.items() if k!='published_file'};portable['file']=stem+'.mp4';target.write_text(json.dumps(portable,indent=2)+'\n',encoding='utf8')
            else:shutil.copyfile(source,target)
            record(target)
        source=ROOT/'media'/timing;target=STAGE/source.name;shutil.copyfile(source,target)
        record(target)
    for filename in ['pa-paper.pdf','pa-paper.tex']:
        target=STAGE/filename;shutil.copyfile(ROOT.parent/'classical'/filename,target);record(target)
    manifest={'tag':'v1.0.0','proofCommit':release['proofCommit'],'theorem':'lw-euler-window-encoded-zero-reduction','paProof':release['paProofReference'],'interpretation':release['interpretationReference'],'films':len(entries),'assets':assets}
    text=json.dumps(manifest,indent=2)+'\n';(ROOT/'release-assets.json').write_text(text,encoding='utf8');(STAGE/'release-assets.json').write_text(text,encoding='utf8')
    print(f'Staged {len(entries)} verified films and {len(assets)+1} release assets under {STAGE}.')


if __name__=='__main__':main()
