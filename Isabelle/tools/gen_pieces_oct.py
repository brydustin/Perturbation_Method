"""Generate the octagon check (copy of gen_pieces.py) as pieces [j/4096, (j+1)/4096], j < 3232 (all 202 sectors k of
width 1/256, 16 pieces each), for the 30-degree band and for no band.  One theory per sector and band;
each piece is a lemma proved by the compiled checker of DC_Tables and logged to logs/sector_progress.log.
usage: gen_pieces_oct.py OUTDIR D [mock]   (mock: sorry instead of checks, session names prefixed Mock)"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.abspath(sys.argv[1]); D = int(sys.argv[2]); MOCK = len(sys.argv) > 3 and sys.argv[3] == "mock"
LOG = os.path.join(OUT, "progress.log") if MOCK else os.path.join(ROOT, "logs", "oct_progress.log")
NK, SUB, NSESS = 202, 16, 24
SP = "Mock" if MOCK else ""
bands = [("c30", "oc_b30"), ("nc", "None")]
def w(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True); open(path, "w").write(text)
def proof(name): return "sorry" if MOCK else f"by (oc_eval {name})"
qd = "quick_and_dirty, " if MOCK else ""
root = []
w(f"{OUT}/Tables/OC_Tables.thy", open(f"{ROOT}/tools/OC_Tables.thy.in").read().replace("@LOG@", LOG).replace("@D@", str(D)))
w(f"{OUT}/Tables/OC_Split.thy", "theory OC_Split\n  imports OC_Tables\nbegin\n\n" + open(f"{ROOT}/tools/OC_Split_body.in").read().replace("@D@", str(D)) + "\nend\n")
root.append(f'session {SP}OC_Tables in "Tables" = DC_Tables +\n  options [{qd}timeout = 0]\n  theories\n    Octagon_Symmetry\n    OC_Tables\n    OC_Split\n')
# interleave cheap and expensive sectors: session s gets k = s, s + NSESS, ...
ks = list(range(NK)); prev = f"{SP}OC_Tables"; allthys = []
for s in range(NSESS):
    mine = ks[s::NSESS]
    names = []
    for k in mine:
        for b, bt in bands:
            name = f"OCX_{b}_{k:03d}"; names.append(name); allthys.append(f'"{SP}OCX_{s}.{name}"')
            js = list(range(SUB * k, SUB * k + SUB))
            lem = [f'lemma oc_{b}_{j:04d}: "oc_sub {bt} {j}"\n  {proof(f"oc_{b}_{j:04d}")}\n' for j in js]
            facts = " ".join(f"oc_{b}_{j:04d}" for j in js)
            sec = f'''lemma upt_{b}_{k:03d}: "[{js[0]}..<{js[-1] + 1}] = [{", ".join(map(str, js))}]"
  by (simp add: upt_rec)

lemma sec_{b}_{k:03d}: "\\<forall>j\\<in>{{16 * {k}..<16 * {k} + 16}}. oc_sub {bt} j"
proof
  fix j :: nat assume "j \\<in> {{16 * {k}..<16 * {k} + 16}}"
  then have "j \\<in> set [{js[0]}..<{js[-1] + 1}]" unfolding set_upt by simp
  then have "j \\<in> set [{", ".join(map(str, js))}]" unfolding upt_{b}_{k:03d} .
  then show "oc_sub {bt} j" using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
            w(f"{OUT}/S{s}/{name}.thy", f'theory {name}\n  imports "{SP}OC_Tables.OC_Tables"\nbegin\n\n' + "\n".join(lem) + "\n" + sec + "\nend\n")
    sess = f"{SP}OCX_{s}"
    root.append(f'session {sess} in "S{s}" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}OC_Tables\n  theories\n' + "".join(f"    {n}\n" for n in names))
    prev = sess
def all_lemma(b, t):
    facts = " ".join(f"sec_{b}_{k:03d}" for k in ks)
    return f'''lemma all_{b}: "k < {NK} \\<Longrightarrow> \\<forall>j\\<in>{{16 * k..<16 * k + 16}}. oc_sub {t} j"
proof -
  assume "k < {NK}"
  then have "k \\<in> set [0..<{NK}]" unfolding set_upt by simp
  then have "k \\<in> set [{", ".join(map(str, ks))}]" unfolding upt_all .
  then show ?thesis using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
final = f'''theory Octagon_Final
  imports "{SP}OC_Tables.OC_Split" {" ".join(allthys)}
begin

lemma upt_all: "[0..<{NK}] = [{", ".join(map(str, ks))}]" by (simp add: upt_rec)

{all_lemma("c30", "oc_b30")}
{all_lemma("nc", "None")}
text \\<open>The octagon stops within {D} corrections for every focus angle and every tie rule,
  with the 30-degree band and with no band.\\<close>

theorem octagon_stops_band30:
  "tie_rule tm ts \\<Longrightarrow> stops_within ocp 9 (Some (pi / 6)) tm ts t {D}"
  by (rule oc_pieces_terminates [OF band30_in [where p = 53, folded oc_b30_def] all_c30])

theorem octagon_stops_no_band:
  "tie_rule tm ts \\<Longrightarrow> stops_within ocp 9 None tm ts t {D}"
  by (rule oc_pieces_terminates [OF band_none all_nc])

ML \\<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles [@{{thm octagon_stops_band30}}, @{{thm octagon_stops_no_band}}])))\\<close>

end
'''
w(f"{OUT}/Final/Octagon_Final.thy", final)
root.append(f'session {SP}OCX_Final in "Final" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}OC_Tables\n  theories\n    Octagon_Final\n')
w(f"{OUT}/ROOT", "\n".join(root))
print(len(allthys), "theories,", len(allthys) * SUB, "piece lemmas,", NSESS, "sessions, last", prev)
