#!/bin/sh
# Usage: zcmd.sh FILE.tex CMDFILE  -- read FILE (may be empty "-") then run the commands in CMDFILE
d="${ZEVES_DIR:-/opt/Z/Z-Eves}"
f="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
c="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
PATH=$HOME/.local/lima/bin:$PATH limactl shell zeves -- sh -c "cd /tmp && { printf 'read \"%s\";\n' '$f'; cat '$c'; printf 'quit;\n'; } | $d/system/lisp -core $d/system/z-eves-pc-linux-cmucl.core -- -libs $d/library/"
