#!/bin/bash
# Open the ITree/UTP theories in Isabelle/jEdit (Isabelle2026), e.g. tools/jedit_utp.sh Hoare/UTP/Perturbative_UTP.thy
cd "$(dirname "$0")/.."
U=/home/dusty/Desktop/Academic/Isabelle_Stuff/IsabelleUTP_2026/src
D="-d . -d Pieces -d Pieces_Oct -d Hoare"
for e in Optics-main Z_Toolkit-main Shallow-Expressions-main Shallow_Expressions_Z Abstract_Prog_Syntax-main \
         Circus_Toolkit interaction-trees explore-subgoal; do D="$D -d $U/$e"; done
exec /home/dusty/Desktop/Isabelle/Isabelle2026/bin/isabelle jedit $D -l Perturbative_UTP_Base "$@"
