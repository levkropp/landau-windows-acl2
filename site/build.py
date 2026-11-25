"""Build the static lesson book locally or after the recorded proof milestone."""
from __future__ import annotations
import argparse,hashlib,html,json,math,re,shutil,subprocess,urllib.request
from html.parser import HTMLParser
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
DIST=HERE/'dist'
ASSETS=('style.css','app.js','math.js','demos.js')
DEMO_TITLES={'odd-squares':'Build a square from odd layers','clock':'Test a successor clock','intervals':'Calculate with exact intervals','grid':'Search the teaching peak','prime-powers':'Find the prime-power contribution','one-sided':'Keep the extra real reading','exponential':'Refine an exponential band','phase':'Refine a rational rotation','circle':'Check a squared-radius gap','window-witness':'Inspect the witness inequalities'}
WORDS=('Zero','One','Two','Three','Four','Five','Six','Seven','Eight','Nine')
SOURCE_PATTERN=re.compile(r'\{\{source:([^:}]+):(defun|defthm):([^}]+)\}\}')


def human(text):
    return text.replace('Landau Windows A C L two','Landau Windows ACL Two').replace('A C L two','ACL2').replace('Z F C','ZFC').replace('Godel','Gödel')


def read_form(path,kind,name):
    text=path.read_text(encoding='utf8')
    match=re.search(r'^\('+re.escape(kind)+r'\s+'+re.escape(name)+r'(?=[\s()])',text,re.M)
    if not match:raise ValueError(f'Missing {kind} {name} in {path}')
    level=0;quoted=False;escaped=False;comment=False
    for i in range(match.start(),len(text)):
        char=text[i]
        if comment:
            if char=='\n':comment=False
            continue
        if quoted:
            if escaped:escaped=False
            elif char=='\\':escaped=True
            elif char=='"':quoted=False
            continue
        if char==';':comment=True
        elif char=='"':quoted=True
        elif char=='(':level+=1
        elif char==')':
            level-=1
            if level==0:return text[match.start():i+1]
    raise ValueError(f'Unclosed source form {name}')


def source_card(match,repository):
    relative,kind,name=match.groups();path=(ROOT/relative).resolve()
    if not path.is_relative_to(ROOT.resolve()):raise ValueError('Source path escapes the repository')
    source=read_form(path,kind,name);digest=hashlib.sha256(source.encode()).hexdigest();url=repository+'/blob/main/'+relative
    return f'<div class="source-card" data-source-file="{html.escape(relative)}" data-source-hash="{digest}"><div class="source-heading"><a href="{html.escape(url)}">{html.escape(name)}</a><button class="copy-code" type="button" hidden>Copy code</button></div><pre><code>{html.escape(source)}</code></pre><p class="source-caption">Complete {kind} form from <a href="{html.escape(url)}">{html.escape(relative)}</a>. Included source, not a browser proof run.</p></div>'


class ArticleParser(HTMLParser):
    def __init__(self):
        super().__init__();self.sections=[];self.ids=[];self.text=[];self.heading=None;self.heading_text=[];self.lead=False;self.summary=[]
    def handle_starttag(self,tag,attrs):
        attrs=dict(attrs)
        if 'id' in attrs:self.ids.append(attrs['id'])
        if tag=='h2':
            if not attrs.get('id'):raise ValueError('Article headings need stable IDs')
            self.heading=attrs['id'];self.heading_text=[]
        if tag=='p' and attrs.get('class')=='lead':self.lead=True
    def handle_endtag(self,tag):
        if tag=='h2' and self.heading is not None:
            self.sections.append({'id':self.heading,'title':''.join(self.heading_text)});self.heading=None
        if tag=='p':self.lead=False
    def handle_data(self,value):
        self.text.append(value)
        if self.heading is not None:self.heading_text.append(value)
        if self.lead:self.summary.append(value)


def load_lessons(episodes,repository):
    lessons=[]
    for episode in episodes:
        if not episode.get('asset'):continue
        path=HERE/'lessons'/f"part-{episode['id']}.html";body=path.read_text(encoding='utf8')
        body=SOURCE_PATTERN.sub(lambda m:source_card(m,repository),body)
        def demo(match):
            name=match[1]
            if name not in DEMO_TITLES:raise ValueError(f'Unknown demo: {name}')
            return f'<section class="demo" data-demo="{name}" aria-label="{DEMO_TITLES[name]}"><p class="eyebrow">Interactive example</p><h3>{DEMO_TITLES[name]}</h3><div class="demo-mount"></div><noscript><p>Enable JavaScript to explore this example. The worked calculation and exercise remain available in the article.</p></noscript><p class="demo-scope">Educational calculation. This demo does not run ACL2 or certify a theorem.</p></section>'
        body=re.sub(r'\{\{demo:([a-z-]+)\}\}',demo,body)
        if '{{' in body:raise ValueError(f'Unexpanded article directive in {path}')
        parser=ArticleParser();parser.feed(body)
        if len(set(parser.ids))!=len(parser.ids):raise ValueError(f'Duplicate heading IDs in {path}')
        if not parser.sections or not parser.summary:raise ValueError(f'Missing article structure in {path}')
        text=' '.join(parser.text)
        lessons.append({**episode,'label':'Part '+WORDS[int(episode['id'])],'url':f"parts/{episode['id']}/",'body':body,'sections':parser.sections,'summary':''.join(parser.summary),'searchText':text,'readingMinutes':max(1,math.ceil(len(text.split())/200))})
    return lessons


def validate_release(release):
    fields=['proofReference','interpretationReference','proofCommit','finalOverviewAsset','publicMediaBase']
    if release['proofMilestone']!='complete' or any(not release.get(x) for x in fields):raise ValueError('Public release is pending the full proof, interpretation and final overview records. Local preview remains available.')
    if not re.fullmatch(r'[a-f0-9]{40}',release['proofCommit']):raise ValueError('Record the actual proof commit before release.')


def web_metadata(timings,title):
    return {'title':title,'chapters':[{'start':s['start'],'chapter':human(s['chapter']),'text':human(' '.join(p['text'] for p in s['sentences']))} for s in timings]}


def collect_films(episodes,release,is_release):
    (DIST/'media').mkdir(parents=True,exist_ok=True);films=[]
    settings=[(ep['id'],Path(ep['asset']).stem,ep['timing'],f"Part {WORDS[int(ep['id'])]} · {ep['title']}") for ep in episodes if ep.get('asset') and ep.get('timing')]
    settings.append(('overview','landau-windows-acl2-overview-05','timing-v5.json','Project overview · The completed reduction'))
    for identity,stem,timing,title in settings:
        if is_release:
            if identity!='overview' and next(ep for ep in episodes if ep['id']==identity)['state'] not in ('ready','published'):continue
            asset=release['finalOverviewAsset'] if identity=='overview' else stem+'.mp4';stem=Path(asset).stem;base=release['publicMediaBase'].rstrip('/')
            with urllib.request.urlopen(base+'/'+stem+'-web.json',timeout=30) as response:meta=json.load(response)
            with urllib.request.urlopen(base+'/'+stem+'.vtt',timeout=30) as response:captions=response.read()
            if not captions.startswith(b'WEBVTT'):raise ValueError('Published captions are missing or invalid.')
            (DIST/'media'/f'{identity}.vtt').write_bytes(captions);src=base+'/'+asset;poster=base+'/'+stem+'-poster.jpg';duration=None
        else:
            timing_path=ROOT/'video/media'/timing
            if not timing_path.exists():continue
            meta=web_metadata(json.loads(timing_path.read_text(encoding='utf8')),title)
            source=ROOT/'video/media'/f'{stem}.mp4'
            if not source.exists():source=ROOT/'video/media'/f'{stem}-preview.mp4'
            src=None;poster=None;duration=None
            if source.exists():
                target=DIST/'media'/f'{identity}.mp4'
                if not target.exists() or target.stat().st_size!=source.stat().st_size or source.stat().st_mtime>target.stat().st_mtime:shutil.copyfile(source,target)
                src=f'media/{identity}.mp4';poster_path=DIST/'media'/f'{identity}.jpg';cached=ROOT/'video/media'/f'{stem}-poster.jpg'
                if cached.exists():shutil.copyfile(cached,poster_path)
                elif not poster_path.exists():subprocess.run(['ffmpeg','-v','error','-y','-ss','18','-i',str(source),'-frames:v','1','-vf','scale=1440:-1',str(poster_path)],check=True)
                poster=f'media/{identity}.jpg';verification=ROOT/'video/media'/f'{stem}-verification.json'
                if verification.exists():duration=float(json.loads(verification.read_text(encoding='utf8'))['format']['duration'])
            shutil.copyfile(ROOT/'video/media'/f'{stem}.vtt',DIST/'media'/f'{identity}.vtt')
        films.append({'id':identity,'title':meta['title'],'src':src,'poster':poster,'captions':f'media/{identity}.vtt','chapters':meta['chapters'],'duration':duration,'note':'Manim animation · Local M2 narration · English captions'})
    return films


def film_html(film,prefix):
    if not film:return '<section id="watch" class="watch"><h2>Watch the lesson</h2><p class="note">The article is available. This film has not been included in this build.</p></section>'
    def asset(value):return value if value.startswith('https://') else prefix+value
    src=f' src="{html.escape(asset(film["src"]))}"' if film.get('src') else '';poster=f' poster="{html.escape(asset(film["poster"]))}"' if film.get('poster') else '';caption=html.escape(asset(film['captions']))
    chapters=[];transcript=[]
    for chapter in film['chapters']:
        stamp=f"{int(chapter['start']//60)}:{int(chapter['start']%60):02}"
        chapters.append(f'<li><a href="#watch" data-seek="{chapter["start"]}"><span class="time">{stamp}</span> {html.escape(chapter["chapter"])}</a></li>')
        transcript.append(f'<h3>{stamp} · {html.escape(chapter["chapter"])}</h3><p>{html.escape(chapter["text"])}</p>')
    return f'<section id="watch" class="watch" aria-labelledby="watch-heading"><h2 id="watch-heading">Watch the lesson</h2><video id="player" controls playsinline preload="none"{src}{poster} aria-label="{html.escape(film["title"])}"><track kind="captions" label="English" srclang="en" src="{caption}" default></video><div class="film-footer"><span>{film["note"]}</span><a href="{caption}" download>Download captions</a></div><details class="chapter-panel"><summary>{len(chapters)} chapters · jump to a section</summary><ol id="chapter-list">{"".join(chapters)}</ol></details><details class="transcript"><summary>Read the narration transcript</summary>{"".join(transcript)}</details></section>'


def render_page(template,lessons,episodes,films,release,is_release,evidence,identity=None):
    prefix='../../' if identity else './';lesson=next((p for p in lessons if p['id']==identity),None);current=next((f for f in films if f['id']==(identity or 'overview')),None);nav=[];completed=release['proofMilestone']=='complete'
    for ep in episodes:
        available=next((p for p in lessons if p['id']==ep['id']),None);label='Part '+WORDS[int(ep['id'])]
        if available:nav.append(f'<a href="{prefix}{available["url"]}"'+(' aria-current="page"' if ep['id']==identity else '')+f'><span>{label}</span>{html.escape(ep["title"])}</a>')
        else:nav.append(f'<span class="pending-lesson"><span>{label} · after the proof</span>{html.escape(ep["title"])}</span>')
    if lesson:
        index=lessons.index(lesson);previous=lessons[index-1] if index else None;following=lessons[index+1] if index+1<len(lessons) else None
        duration=f" · {math.ceil(current['duration']/60)} min video" if current and current.get('duration') else ''
        top=f'<header class="lesson-header"><p class="eyebrow">{lesson["label"]}{duration} · {lesson["readingMinutes"]} min read</p><h1>{html.escape(lesson["title"])}</h1><p>{html.escape(lesson["summary"])}</p><div class="lesson-jumps"><a href="#watch">Watch</a><a href="#follow-along">Read</a><a href="#interactive">Try it</a></div></header>'
        body=lesson['body'].replace('<section class="demo"','<section id="interactive" class="demo"',1)
        if completed and int(lesson['id'])<9:body=f'<p class="note">This film records an earlier stage of the project. <a href="{prefix}parts/09/">Part Nine</a> explains the completed reduction and the obligations subsequently discharged.</p>'+body
        pagination='<nav class="page-turns" aria-label="Previous and next lesson">'
        for item,label in [(previous,'Previous lesson'),(following,'Next lesson')]:
            if item:pagination+=f'<a href="{prefix}{item["url"]}"><span>{label} · {item["label"]}</span>{html.escape(item["title"])}</a>'
        pagination+='</nav>';main=top+film_html(current,prefix)+f'<article id="follow-along" class="article"><div class="article-title"><p class="eyebrow">Follow-along article</p><p>Read, calculate, then compare with the source.</p></div>{body}</article>'+pagination
        toc='<a href="#watch">Video and chapters</a><a href="#follow-along">Follow-along article</a>'+''.join(f'<a href="#{s["id"]}">{html.escape(s["title"])}</a>' for s in lesson['sections']);title=f'{lesson["label"]}: {lesson["title"]}';description=lesson['summary']
    else:
        cards=''.join(f'<li><a href="{prefix}{p["url"]}"><span class="eyebrow">{p["label"]}</span><h3>{html.escape(p["title"])}</h3><p>{html.escape(p["topics"])}</p><span class="lesson-reading">Video · article · interactive example</span></a></li>' for p in lessons)
        state='The encoded windowed Landau ceiling reduction is proved in first-order Peano Arithmetic, with the corresponding development certified in vanilla ACL2. The PA manuscript gives the direct proof in Theorem 15.2 and supplies the classical zeta correspondence. Part Nine explains the hypotheses, computed threshold and returned rational witness.' if completed else 'Part Nine is reserved for the completed ACL2 reduction and its intended Peano Arithmetic interpretation. The current lessons explain certified components and conditional results; they do not announce that milestone.'
        main=f'<header class="home-header"><p class="eyebrow">A visual course with worked mathematics</p><h1>From whole numbers<br>to the Landau bridge.</h1><p>Follow the films, work through the articles, and experiment with exact arithmetic. Build the finite constructions behind one classical bridge between prime-counting errors and zeta zeros.</p><a class="primary" href="{prefix}parts/00/">Start with Part Zero</a></header><section id="course"><h2>Follow the argument, one part at a time</h2><p>Start with undergraduate discrete mathematics. Each lesson introduces the tools used by the next. There are nine lessons, including Part Zero.</p><ol class="course-grid">{cards}</ol></section><section id="proof" class="proof-note"><p class="eyebrow">The research milestone</p><h2>The final reduction comes next</h2><p>{state}</p><p>{html.escape(evidence)}</p><a href="{html.escape(release["repositoryUrl"])}/blob/main/docs/reduction-status.md">Read the current proof obligations and evidence</a></section><section id="overview"><h2>Project overview</h2><p>The original overview gives the motivation. The lesson articles carry the more detailed definitions, qualifications and worked examples.</p>{film_html(current,prefix)}</section>'
        toc='<a href="#course">The lessons</a><a href="#proof">Proof status</a><a href="#overview">Project overview</a>';title='From arithmetic to the Landau bridge';description='A visual course with videos, worked articles and interactive exact-arithmetic examples, from Peano Arithmetic to the Landau bridge.'
        main=main.replace('There are nine lessons, including Part Zero.',f'There are {len(lessons)} lessons, including Part Zero.')
        if completed:
            main=main.replace('The final reduction comes next','Proved in Peano Arithmetic')
            main=main.replace('Read the current proof obligations and evidence','Read the proof ledger and evidence')
            main=main.replace('The original overview gives the motivation.','The completed overview explains the motivation and the result.')
            main=main.replace('</p><p>'+html.escape(evidence),'</p><p><a href="'+html.escape(release['repositoryUrl'])+'/blob/main/classical/pa-paper.pdf">Read the Peano Arithmetic proof manuscript (PDF)</a></p><p>'+html.escape(evidence))
        feature=main.index('<section id="overview">');course=main.index('<section id="course">')
        main=main[:course]+main[feature:]+main[course:feature]
        toc='<a href="#overview">Project overview</a><a href="#course">The lessons</a><a href="#proof">Proof and interpretation</a>'
    search=[{k:p[k] for k in ('id','label','title','url','summary','sections','searchText')} for p in lessons]
    data={'rootPath':prefix,'released':is_release,'episode':identity,'film':current,'films':[{k:v for k,v in f.items() if k!='chapters'} for f in films],'lessons':search,'evidence':evidence};canonical=release['siteUrl'].rstrip('/')+'/'+(lesson['url'] if lesson else '')
    values={'TITLE':html.escape(title),'DESCRIPTION':html.escape(description),'ROOT':prefix,'NAV':''.join(nav),'TOC':toc,'MAIN':main,'REPOSITORY':html.escape(release['repositoryUrl']),'EDITION':'Completed edition' if is_release else ('Local preview · completed reduction' if completed else 'Review edition · reduction in progress'),'CANONICAL':f'<link rel="canonical" href="{html.escape(canonical)}">' if is_release else '<meta name="robots" content="noindex">','DATA':json.dumps(data,ensure_ascii=False).replace('</','<\\/').replace('\u2028','\\u2028').replace('\u2029','\\u2029')}
    for name,value in values.items():template=template.replace('__'+name+'__',value)
    return template


def main():
    parser=argparse.ArgumentParser();mode=parser.add_mutually_exclusive_group();mode.add_argument('--release',action='store_true');mode.add_argument('--check',action='store_true',help='Validate articles and source references without media or network');args=parser.parse_args();release=json.loads((ROOT/'video/release.json').read_text(encoding='utf8'))
    if args.release:
        try:validate_release(release)
        except ValueError as error:raise SystemExit(str(error))
    series=json.loads((ROOT/'video/series.json').read_text(encoding='utf8'));lessons=load_lessons(series['episodes'],release['repositoryUrl'])
    if args.check:print(f'Validated {len(lessons)} articles, source forms and demo references.');return
    films=collect_films(series['episodes'],release,args.release);ledger=(ROOT/'docs/reduction-status.md').read_text(encoding='utf8');match=re.search(r'These are ([\w-]+) ACL2 books with ([\d,]+) exported theorems',ledger)
    evidence=f'{match[1].replace("-"," ").capitalize()} ACL2 books · {match[2]} exported theorems, as recorded in the proof ledger.' if match else 'Certified components and remaining obligations are recorded in the proof ledger.'
    template=(HERE/'index.html').read_text(encoding='utf8');(DIST/'index.html').write_text(render_page(template,lessons,series['episodes'],films,release,args.release,evidence),encoding='utf8')
    for lesson in lessons:
        destination=DIST/lesson['url'];destination.mkdir(parents=True,exist_ok=True);(destination/'index.html').write_text(render_page(template,lessons,series['episodes'],films,release,args.release,evidence,lesson['id']),encoding='utf8')
    for name in ASSETS:shutil.copyfile(HERE/name,DIST/name)
    (DIST/'.nojekyll').touch();print(f'Built {DIST} ({"release" if args.release else "local review"}); {len(lessons)} lesson articles, {len(films)} films.')


if __name__=='__main__':main()
