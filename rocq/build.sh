#!/bin/sh
# Build the UPRF Rocq development (requires rocq and the MathComp/mczify packages).
cd "$(dirname "$0")"
rocq makefile --no-rocq-package-warning -f _CoqProject -o Makefile > /dev/null && make -s "$@" 2>&1
