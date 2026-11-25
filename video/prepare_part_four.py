"""Certify Part Four against isolated snapshots of the project dependencies."""
from __future__ import annotations
import hashlib,json,re,shlex,subprocess,time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent
STAGE=ROOT/".tools/acl2-part04"


def wsl_path(path):
    path=path.resolve()
    return "/mnt/"+path.drive[0].lower()+path.as_posix()[2:]


def prepare():
    ordered=[];seen=set();sources={}
    def visit(name):
        if name in seen:return
        seen.add(name)
        data=(REPO/"acl2"/(name+".lisp")).read_bytes()
        for dependency in re.findall(r'^\(include-book "([a-z0-9-]+)"',data.decode("utf8"),re.M):
            visit(dependency)
        ordered.append(name);sources[name]=data
    visit("signal-bounds")
    teacher=(ROOT/"teaching-part04.lisp").read_bytes()
    hashes={name:hashlib.sha256(data).hexdigest() for name,data in sources.items()}
    hashes["teaching-part04"]=hashlib.sha256(teacher).hexdigest()
    fingerprint=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest()
    marker=STAGE/"certified-sources.json"
    expected=[STAGE/"acl2"/(name+".cert") for name in ordered]+[STAGE/"video/teaching-part04.cert"]
    if marker.exists() and json.loads(marker.read_text(encoding="utf8")).get("fingerprint")==fingerprint and all(p.exists() for p in expected):
        print(f"Part Four: {len(expected)} isolated book certificates are current.")
        return
    for name,data in sources.items():
        path=STAGE/"acl2"/(name+".lisp");path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    target=STAGE/"video/teaching-part04.lisp";target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(teacher)
    commands=[]
    for path in [STAGE/"acl2"/name for name in ordered]+[target.with_suffix("")]:
        commands.extend([f'(certify-book "{wsl_path(path)}" 0)',"(ubt! 1)"])
    commands.append("(good-bye)")
    script=STAGE/"certify.lsp";script.write_text("\n".join(commands)+"\n",encoding="utf8")
    log=STAGE/"certify.log";started=time.time()
    command="cd "+shlex.quote(wsl_path(REPO))+" && sh acl2/run-wsl.sh < "+shlex.quote(wsl_path(script))+" > "+shlex.quote(wsl_path(log))+" 2>&1"
    subprocess.run(["wsl","-e","sh","-c",command],check=True)
    output=log.read_text(encoding="utf8",errors="replace")
    if "******** FAILED ********" in output or any(not p.exists() or p.stat().st_mtime<started-2 for p in expected):
        raise RuntimeError("Isolated certification failed; inspect "+str(log))
    marker.write_text(json.dumps({"fingerprint":fingerprint,"source_hashes":hashes,"books":ordered},indent=2),encoding="utf8")
    print(f"Part Four: certified {len(expected)} isolated books. Log: {log}")


if __name__=="__main__":prepare()
