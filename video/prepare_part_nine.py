"""Audit the completed proof and freeze the source shown in the final lesson."""
from __future__ import annotations
import hashlib,json,re,shlex,subprocess
from datetime import datetime,timezone
from pathlib import Path

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent
STAGE=ROOT/".tools/acl2-part09"


def wsl_path(path):
    path=path.resolve()
    return "/mnt/"+path.drive[0].lower()+path.as_posix()[2:]


def prepare():
    script=(REPO/"acl2/certify-wsl.sh").read_text(encoding="utf8")
    books=re.search(r'^  set -- (.*)$',script,re.M).group(1).split()
    ordered=[];seen=set()
    def visit(name):
        if name in seen:return
        seen.add(name)
        for dependency in re.findall(r'^\(include-book "([a-z0-9-]+)"',(REPO/"acl2"/(name+".lisp")).read_text(encoding="utf8"),re.M):visit(dependency)
        ordered.append(name)
    visit("euler-window-encoded-zero")
    hashes={};theorems=0
    for name in books:
        source=REPO/"acl2"/(name+".lisp");certificate=source.with_suffix(".cert")
        if not certificate.exists() or certificate.stat().st_mtime<source.stat().st_mtime:raise RuntimeError("Missing or stale certificate: "+name)
        data=source.read_bytes();text=data.decode("utf8")
        if re.search(r'^\s*\((skip-proofs|defaxiom|defttag|defattach)\b',text,re.M):raise RuntimeError("Review proof-trust event in "+name)
        theorems+=len(re.findall(r'^\(defthm ',text,re.M));hashes["acl2/"+name+".lisp"]=hashlib.sha256(data).hexdigest()
        destination=STAGE/"acl2"/source.name;destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(data)
    for relative in ["docs/acl2-interpretation.md","docs/foundations.md","classical/pa-paper.tex","classical/pa-paper.pdf"]:
        data=(REPO/relative).read_bytes();hashes[relative]=hashlib.sha256(data).hexdigest()
        target=STAGE/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    fingerprint=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest()
    marker=STAGE/"certified-sources.json"
    if marker.exists() and json.loads(marker.read_text(encoding="utf8")).get("fingerprint")==fingerprint:
        print(f"Part Nine: audited snapshot current ({len(books)} books, {theorems} exported theorems).")
        return
    check=STAGE/"check-final.lsp"
    check.write_text(f'(include-book "{wsl_path(REPO/"acl2/euler-window-encoded-zero")}")\n(value-triple :landau-final-book-checked)\n(good-bye)\n',encoding="utf8")
    log=STAGE/"check-final.log"
    command="cd "+shlex.quote(wsl_path(REPO))+" && sh acl2/run-wsl.sh < "+shlex.quote(wsl_path(check))+" > "+shlex.quote(wsl_path(log))+" 2>&1"
    subprocess.run(["wsl","-e","sh","-c",command],check=True)
    output=log.read_text(encoding="utf8",errors="replace")
    if "******** FAILED ********" in output or ":LANDAU-FINAL-BOOK-CHECKED" not in output:raise RuntimeError("Final certificate import failed: "+str(log))
    natural_log=REPO/"acl2/.tools/audit-window-natural-measures.log"
    natural=natural_log.read_text(encoding="utf8")
    match=re.search(r':RECURSIVE\s+(\d+)\s+:EXCEPTIONS NIL',natural)
    if not match:raise RuntimeError("Natural-measure audit evidence missing")
    report={"checked_utc":datetime.now(timezone.utc).isoformat(),"main_theorem":"lw-euler-window-encoded-zero-reduction","default_books":len(books),"exported_theorems":theorems,"final_dependency_books":len(ordered),"certificates_present_and_fresh":True,"final_certificate_import":"passed","forbidden_trust_event_scan":"passed","natural_measure_recursive_definitions":int(match.group(1)),"natural_measure_exceptions":[],"natural_measure_log_sha256":hashlib.sha256(natural_log.read_bytes()).hexdigest(),"source_hashes":hashes,"pa_proof":"classical/pa-paper.tex, Theorem 15.2: a direct mathematical proof in first-order Peano Arithmetic of the encoded windowed ceiling reduction.","classical_comparison":"Supplied in the manuscript's final comparison section and docs/acl2-interpretation.md.","machine_certificate":"Vanilla ACL2 certification; the direct Peano Arithmetic proof is the manuscript, rather than a second machine-checker replay."}
    (REPO/"docs/certification-audit.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
    marker.write_text(json.dumps({"fingerprint":fingerprint,"source_hashes":hashes,"dependency_order":ordered,"audit":{k:v for k,v in report.items() if k!="source_hashes"}},indent=2),encoding="utf8")
    print(f"Part Nine: {len(books)} fresh book certificates, {theorems} exported theorems; final {len(ordered)}-book certificate closure imported successfully.")


if __name__=="__main__":prepare()
