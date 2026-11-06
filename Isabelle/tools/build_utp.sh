#!/bin/bash
# Build an ITree/UTP session of this project (default Perturbative_UTP) under Isabelle2026.
cd "$(dirname "$0")/.."
U=/home/dusty/Desktop/Academic/Isabelle_Stuff/IsabelleUTP_2026/src
D="-d . -d Pieces -d Pieces_Oct -d Hoare"
for e in Optics-main Z_Toolkit-main Shallow-Expressions-main Shallow_Expressions_Z Abstract_Prog_Syntax-main \
         Circus_Toolkit interaction-trees explore-subgoal; do D="$D -d $U/$e"; done
exec /home/dusty/Desktop/Isabelle/Isabelle2026/bin/isabelle build -j 1 -o threads=8 $D "$@"
