set -eu

apt-get update -qq
apt-get install -y --no-install-recommends sbcl acl2-source
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
runtime_root="$task_root/acl2/.tools/runtime"
source_root=$(dpkg-query -L acl2-source | sed -n 's@/acl2.lisp$@@p' | head -n 1)
mkdir -p "$runtime_root"
cp -a "$source_root"/. "$runtime_root/"
cd "$runtime_root"
bash "$task_root/acl2/compile-wsl.sh"
bash "$task_root/acl2/save-wsl.sh"
