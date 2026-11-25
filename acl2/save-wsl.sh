set -eu

task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root/acl2/.tools/runtime"
export LC_ALL=C
sbcl --noinform --non-interactive --load "$task_root/acl2/save-runtime.lisp" > save.log 2>&1
