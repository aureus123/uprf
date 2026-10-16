#!/bin/sh
# Usage: ./pdf.sh   -- typesets uprf.tex into uprf.pdf with pdflatex
# The style file z-eves.sty is taken from the Z/EVES distribution (ZEVES_DIR, default
# /opt/Z/Z-Eves): directly on Linux, from the Lima VM (ZEVES_VM, default zeves) on macOS.
set -e
cd "$(dirname "$0")"
dir="${ZEVES_DIR:-/opt/Z/Z-Eves}"
mkdir -p build
if [ ! -f build/z-eves.sty ]; then
  if [ "$(uname)" = Linux ]; then cp "$dir/z-eves.sty" build/
  else limactl shell "${ZEVES_VM:-zeves}" -- cat "$dir/z-eves.sty" > build/z-eves.sty; fi
fi
for i in 1 2; do
  TEXINPUTS=build:: pdflatex -interaction=nonstopmode -halt-on-error -output-directory build \
    -jobname uprf '\input{pdfsetup}\input{uprf}' > build/pdflatex.out || { tail -20 build/pdflatex.out; exit 1; }
done
cp build/uprf.pdf .
echo "uprf.pdf: $(grep -o '[0-9]* pages' build/pdflatex.out)"
