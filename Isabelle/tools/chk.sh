#!/bin/bash
# Fast check of one theory against the prebuilt Perturbative_Base heap of Isabelle2026.
# usage: tools/chk.sh THEORY [TIMEOUT] [seq]   (seq: parallel_proofs=0 and "@@ N" markers)
# The copy in /tmp/pt_chk imports the other project theories session-qualified, so they are
# loaded from source via -d . (build the Perturbative_Termination heap to speed this up).
D=$(cd "$(dirname "$0")/.." && pwd); T=$1; TO=${2:-600}
N=/tmp/pt_chk; mkdir -p "$N"
python3 - "$D/$T.thy" "$N/$T.thy" "$3" <<'PY'
import sys,re
src,dst,seq=sys.argv[1:4]
s=open(src).read()
m=re.search(r'imports(.*?)\nbegin',s,re.S)
new=' '.join(i if ('.' in i or i.startswith('"')) else '"Perturbative_Termination.%s"'%i for i in m.group(1).split())
s=s[:m.start(1)]+' '+new+s[m.end(1):]
if seq=='seq':
    out=[]
    for i,l in enumerate(s.split('\n'),1):
        if re.match(r'^(lemma|theorem|corollary|proposition|definition|fun|primrec)\b',l):
            out.append('ML \\<open>writeln "@@ %d"\\<close>'%i)
        out.append(l)
    s='\n'.join(out)
open(dst,'w').write(s)
PY
cd "$D"; PP="-o parallel_proofs=2"; [ "$3" = seq ] && PP="-o parallel_proofs=0"
setsid ~/Desktop/Isabelle/Isabelle2026/bin/isabelle process_theories -d . -D "$N" -l Perturbative_Termination -O -U $PP "$T" > "$N/$T.log" 2>&1 &
PID=$!
kill_tree() { for c in $(pgrep -P "$1"); do kill_tree "$c"; done; kill -KILL "$1" 2>/dev/null; }
( t=0; while kill -0 "$PID" 2>/dev/null && [ "$t" -lt "$TO" ]; do sleep 1; t=$((t+1)); done
  if kill -0 "$PID" 2>/dev/null; then touch "$N/$T.timeout"; kill_tree "$PID"; fi ) &
wait "$PID"; RC=$?
[ -f "$N/$T.timeout" ] && { RC=124; rm -f "$N/$T.timeout"; }
echo "EXIT $RC"; grep -n -B2 -A12 '^\*\*\*' "$N/$T.log" | grep -v "^.*Perturbative_Termination\." | head -60; grep -n '@@' "$N/$T.log" | tail -2
