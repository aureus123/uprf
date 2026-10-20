#!/bin/sh
# Builds ../uprf.pdf from ../text/uprf.miz (statements only) with pdfLaTeX.
# Needs Python 3, pdflatex, and the fm.bib of the Mizar distribution
# (default: ../system/doc/fm.bib; set FMBIB to override).
cd "$(dirname "$0")"
FMBIB=${FMBIB:-../system/doc/fm.bib}
python3 miz2tex.py ../text/uprf.miz > body.tex || exit 1
python3 bib.py ../text/uprf.miz "$FMBIB" uprf.tex > refs.tex || exit 1
for i in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error uprf.tex > uprf.build.log || {
    grep -A5 '^!' uprf.build.log; exit 1; }
done
cp uprf.pdf ../uprf.pdf
rm -f uprf.aux uprf.log uprf.out uprf.pdf
echo "OK: ../uprf.pdf"
