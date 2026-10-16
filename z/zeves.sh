#!/bin/sh
# Usage: ./zeves.sh FILE.tex
# Checks a Z/LaTeX specification with Z/EVES 2.3 (text mode): reads the paragraphs, runs the
# zproof scripts and prints the proof status.
#
# Z/EVES only exists as a 32-bit Linux (CMUCL) program.  On Linux it is run directly; on macOS
# it is run inside a Lima VM (default name "zeves") whose home directory mount makes FILE visible.
#   ZEVES_DIR  Z/EVES root directory (containing system/ and library/), default /opt/Z/Z-Eves
#   ZEVES_VM   Lima instance used on macOS, default zeves
dir="${ZEVES_DIR:-/opt/Z/Z-Eves}"
file="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
cmd="printf 'read \"%s\";\nprint status;\nquit;\n' '$file' |
  $dir/system/lisp -core $dir/system/z-eves-pc-linux-cmucl.core -- -libs $dir/library/"
if [ "$(uname)" = Linux ]; then sh -c "$cmd"; else limactl shell "${ZEVES_VM:-zeves}" -- sh -c "cd /tmp && $cmd"; fi
