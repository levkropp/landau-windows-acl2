set -eu

task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root/acl2/.tools/runtime"
export LC_ALL=C
if [ -f ./nsaved_acl2.core ]; then
  exec sbcl --dynamic-space-size 4096 --control-stack-size 64 --core ./nsaved_acl2.core \
    --noinform --disable-debugger --eval '(acl2::sbcl-restart)'
fi
exec sbcl --noinform --disable-debugger --load acl2.lisp \
  --eval '(acl2::load-acl2)' --eval '(acl2::initialize-acl2)' --eval '(acl2::lp)'
