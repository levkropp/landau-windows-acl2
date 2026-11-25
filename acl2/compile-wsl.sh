set -eu

task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root/acl2/.tools/runtime"
python3 -c 'from pathlib import Path; Path("acl2-characters").write_bytes(bytes(range(256)))'
export LC_ALL=C
sbcl --noinform --non-interactive --load acl2.lisp --eval '(acl2::compile-acl2)' > compile.log 2>&1
