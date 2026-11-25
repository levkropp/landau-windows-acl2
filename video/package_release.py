"""Publish lesson media in Git and stage only the final overview for release."""
from __future__ import annotations
import hashlib,json,shutil
from pathlib import Path

ROOT=Path(__file__).resolve().parent
STAGE=ROOT/'.tools/release-overview-v1.0.0'
PUBLISHED=ROOT/'published'


def main():
    release=json.loads((ROOT/'release.json').read_text(encoding='utf8'))
    episodes=json.loads((ROOT/'series.json').read_text(encoding='utf8'))['episodes']
    entries=[('part-'+ep['id'],Path(ep['asset']).stem,ep['timing']) for ep in episodes]
    entries.append(('overview',Path(release['finalOverviewAsset']).stem,'timing-v5.json'))
    STAGE.mkdir(parents=True,exist_ok=True);assets=[];repository=[]
    def record(path,collection,name):
        with path.open('rb') as stream:digest=hashlib.file_digest(stream,'sha256').hexdigest()
        collection.append({'file':name,'bytes':path.stat().st_size,'sha256':digest})
    def copy_text(source,target):
        target.write_bytes(source.read_bytes().replace(b'\r\n',b'\n').rstrip(b'\n')+b'\n')
    for identity,stem,timing in entries:
        verification=json.loads((ROOT/'media'/f'{stem}-verification.json').read_text(encoding='utf8'))
        if verification.get('full_decode')!='passed' or verification.get('caption_and_audio_bounds')!='passed':raise RuntimeError('Unverified movie: '+stem)
        folder=PUBLISHED/identity;folder.mkdir(parents=True,exist_ok=True)
        source=ROOT/'media'/f'{stem}.mp4'
        if identity=='overview':
            target=STAGE/source.name;shutil.copyfile(source,target);record(target,assets,target.name)
        else:
            if source.stat().st_size>=100*1024*1024:raise RuntimeError('Movie exceeds the regular Git file limit: '+stem)
            target=folder/'film.mp4';shutil.copyfile(source,target);record(target,repository,target.relative_to(ROOT.parent).as_posix())
        companions={'.vtt':'captions.vtt','.srt':'captions.srt','-poster.jpg':'poster.jpg','-web.json':'chapters.json','-transcript.md':'transcript.md','-chapters.txt':'chapters.txt','-verification.json':'verification.json'}
        for suffix,filename in companions.items():
            target=folder/filename
            if suffix=='-verification.json':
                portable={k:v for k,v in verification.items() if k!='published_file'}
                portable['file']=release['publicMediaBase']+'/'+source.name if identity=='overview' else 'film.mp4'
                target.write_bytes((json.dumps(portable,indent=2)+'\n').encode('utf8'))
            elif suffix=='-poster.jpg':shutil.copyfile(ROOT/'media'/(stem+suffix),target)
            else:copy_text(ROOT/'media'/(stem+suffix),target)
            record(target,repository,target.relative_to(ROOT.parent).as_posix())
        target=folder/'timing.json';copy_text(ROOT/'media'/timing,target);record(target,repository,target.relative_to(ROOT.parent).as_posix())
    for filename in ['pa-paper.pdf','pa-paper.tex']:
        path=ROOT.parent/'classical'/filename;record(path,repository,path.relative_to(ROOT.parent).as_posix())
    manifest={'tag':'v1.0.0','proofCommit':release['proofCommit'],'theorem':'lw-euler-window-encoded-zero-reduction','paProof':release['paProofReference'],'interpretation':release['interpretationReference'],'films':len(entries),'assets':assets,'repositoryFiles':repository}
    (ROOT/'release-assets.json').write_bytes((json.dumps(manifest,indent=2)+'\n').encode('utf8'))
    print(f'Published ten lesson MP4s and their companion files under {PUBLISHED}.')
    print(f'Staged only the final overview MP4 under {STAGE}.')


if __name__=='__main__':main()
