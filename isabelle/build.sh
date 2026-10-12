#!/bin/bash
# Build the UPRF session; print theory progress, errors and long-running commands.
#   ISABELLE  the isabelle executable (default: isabelle, from PATH)
#   AFP       directory containing the AFP entry Recursion-Theory-I (default: ./afp)
cd "$(dirname "$0")"
ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-afp}"
"$ISABELLE" build -v -d "$AFP/Recursion-Theory-I" -D UPRF 2>&1 \
  | grep -E --line-buffered "theory UPRF|\*\*\*|Finished|FAILED|Timeout|running for [0-9]{2}" \
  | grep -v --line-buffered "cumulated" | awk '!seen[$0]++ {print; fflush()}'
