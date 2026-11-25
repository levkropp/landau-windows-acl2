"""Static-site checks that require neither video binaries nor network access."""
import importlib.util,json,re,tempfile,unittest
from pathlib import Path
from html.parser import HTMLParser

SITE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('lesson_site_builder',SITE/'build.py')
builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)


class Structure(HTMLParser):
    def __init__(self):super().__init__();self.ids=[];self.links=[];self.titles=0
    def handle_starttag(self,tag,attrs):
        data=dict(attrs)
        if 'id' in data:self.ids.append(data['id'])
        if tag=='a' and data.get('href','').startswith('#'):self.links.append(data['href'][1:])
        if tag=='h1':self.titles+=1


class SiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.release=json.loads((SITE.parent/'video/release.json').read_text(encoding='utf8'))
        cls.episodes=json.loads((SITE.parent/'video/series.json').read_text(encoding='utf8'))['episodes']
        cls.lessons=builder.load_lessons(cls.episodes,cls.release['repositoryUrl'])
        cls.template=(SITE/'index.html').read_text(encoding='utf8')
    def test_every_lesson_has_worked_article_and_demo(self):
        self.assertEqual([x['id'] for x in self.lessons],[f'{i:02}' for i in range(10)])
        for lesson in self.lessons:
            self.assertGreaterEqual(len(lesson['sections']),5)
            self.assertEqual(lesson['body'].count('class="demo"'),1)
            self.assertIn('<details>',lesson['body'])
            self.assertNotIn('{{',lesson['body'])
    def test_routes_and_anchors_resolve_in_every_rendered_page(self):
        for identity in [None]+[x['id'] for x in self.lessons]:
            document=builder.render_page(self.template,self.lessons,self.episodes,[],self.release,False,'audit evidence',identity)
            parsed=Structure();parsed.feed(document)
            self.assertEqual(len(parsed.ids),len(set(parsed.ids)),identity)
            self.assertEqual(parsed.titles,1)
            self.assertFalse(set(parsed.links)-set(parsed.ids),(identity,set(parsed.links)-set(parsed.ids)))
            self.assertIn('../../app.js' if identity else './app.js',document)
            self.assertNotRegex(document,r'__(?:ROOT|MAIN|DATA|TITLE)__')
    def test_public_page_has_canonical_and_no_local_paths(self):
        document=builder.render_page(self.template,self.lessons,self.episodes,[],self.release,True,'audit evidence','09')
        self.assertIn('rel="canonical"',document)
        self.assertIn('/parts/09/',document)
        self.assertNotIn('content="noindex"',document)
        self.assertNotIn('C:\\Users',document)
    def test_release_gate_rejects_missing_evidence(self):
        incomplete={**self.release,'proofMilestone':'in-progress'}
        with self.assertRaises(ValueError):builder.validate_release(incomplete)
        invalid={**self.release,'proofCommit':'short'}
        with self.assertRaises(ValueError):builder.validate_release(invalid)
        builder.validate_release(self.release)
    def test_lisp_extraction_ignores_comments_and_quoted_parentheses(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'book.lisp';path.write_text('(defun demo (x)\n ; ) comment\n (list "(" x))\n(defun other () 0)',encoding='utf8')
            self.assertEqual(builder.read_form(path,'defun','demo'),'(defun demo (x)\n ; ) comment\n (list "(" x))')


if __name__=='__main__':unittest.main()
