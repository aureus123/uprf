#!/bin/bash
# Open the UPRF theories in Isabelle/jEdit, with the Recursion-Theory-I session as logic.
# Usage: ./jedit.sh [theory files...]   (default: UPRF/UPRF_Robinson.thy)
#   ISABELLE  the isabelle executable (default: isabelle, from PATH)
#   AFP       directory containing the AFP entry Recursion-Theory-I (default: ./afp)
cd "$(dirname "$0")"
ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-afp}"
[ $# -eq 0 ] && set -- UPRF/UPRF_Robinson.thy
exec "$ISABELLE" jedit -d "$AFP/Recursion-Theory-I" -d UPRF -l Recursion-Theory-I "$@"
