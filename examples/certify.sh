#!/bin/sh
# Certify one or more example books with the laptop's ACL2, one certify at a
# time machine-wide (a mkdir lock; no flock on macOS).
#
#   examples/certify.sh induction/app-assoc.lisp ...      (paths relative to examples/)
#
# ACL2: the fn toolchain's qualified build, ACL2 8.7 on SBCL 2.6.8
# (~/tools/acl2-fn, built by ~/dev/fn/tools/build_local_acl2.sh). Override
# with ACL2=... and ACL2_SYSTEM_BOOKS=... . cert.pl is the community build
# tool (:doc build::cert.pl).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${ACL2:=$HOME/tools/acl2-fn/acl2-literal-4g-tls64k}"
: "${ACL2_SYSTEM_BOOKS:=$HOME/tools/acl2-fn/acl2-8.7/books}"
export ACL2 ACL2_SYSTEM_BOOKS
lock="$here/.cert.lock"
i=0
until mkdir "$lock" 2>/dev/null; do
  i=$((i+1)); [ $((i % 30)) -eq 0 ] && echo "certify.sh: waiting for $lock ($((i))s)" >&2
  sleep 1
done
trap 'rmdir "$lock" 2>/dev/null' EXIT INT TERM
cd "$here"
exec perl "$ACL2_SYSTEM_BOOKS/build/cert.pl" --acl2 "$ACL2" "$@"
