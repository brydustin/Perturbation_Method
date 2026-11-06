"""Generate parts 2-13 of the double-cross check as pieces [j/4096, (j+1)/4096], 256 <= j < 3232,
on top of DC_Sectors_0 (sectors k < 16 of width 1/256).  One theory per sector k and band;
each piece is a lemma proved by the compiled checker of DC_Tables, logged to logs/sector_progress.log.
usage: gen_sectors2.py OUTDIR [mock]   (mock: sorry instead of checks, and a stub DC_Sectors_0)"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.abspath(sys.argv[1]); MOCK = len(sys.argv) > 2 and sys.argv[2] == "mock"
LOG = os.path.join(ROOT, "logs", "sector_progress.log") if not MOCK else os.path.join(OUT, "progress.log")
K0, K1, SUB, NSESS = 16, 202, 16, 24
SP = "Mock" if MOCK else ""   # session-name prefix, so a mock never touches the real heaps
bands = [("c30", "dc_b30"), ("nc", "None")]
def w(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True); open(path, "w").write(text)
def proof(name): return "sorry" if MOCK else f"by (dc_eval {name})"
root = []
if MOCK:   # stub of part 1 with the same lemma statements
    lem = []
    for k in range(K0):
        for b, t in [("c30", "Some (band30 53)"), ("nc", "None")]:
            lem.append(f'lemma dc_{b}_{k:03d}: "check_sector 53 dc_q 9 inv9_ivl ({t}) 20 (Float 1 (-26)) 100 (Float (int {k}) (-8)) (Float (int {k} + 1) (-8))"\n  sorry\n')
    w(f"{OUT}/Old/DCS_0_00.thy", 'theory DCS_0_00\n  imports "Perturbative_Termination.Double_Cross"\nbegin\n\n' + "\n".join(lem) + "\nend\n")
    root.append(f'session {SP}DC_Sectors_0 in "Old" = Perturbative_Termination +\n  options [quick_and_dirty]\n  theories\n    DCS_0_00\n')
    old_thys = [f'"{SP}DC_Sectors_0.DCS_0_00"']
else:
    old_thys = [f'"{SP}DC_Sectors_0.DCS_0_{i:02d}"' for i in range(4)]
w(f"{OUT}/Tables/DC_Tables.thy", open(f"{ROOT}/tools/DC_Tables.thy.in").read().replace("@LOG@", LOG))
w(f"{OUT}/Tables/DC_Split.thy", "theory DC_Split\n  imports DC_Tables\nbegin\n\n" + open(f"{ROOT}/tools/DC_Split_body.in").read() + "\nend\n")
qd = "quick_and_dirty, " if MOCK else ""
root.append(f'session {SP}DC_Tables in "Tables" = {SP}DC_Sectors_0 +\n  options [{qd}timeout = 0]\n  sessions Perturbative_Termination\n  theories\n    DC_Tables\n    DC_Split\n')
ks = list(range(K0, K1)); per = -(-len(ks) // NSESS); prev = f"{SP}DC_Tables"; allthys = []
for s in range(NSESS):
    mine = ks[s * per:(s + 1) * per]
    if not mine: break
    names = []
    for k in mine:
        for b, bt in bands:
            name = f"DCX_{b}_{k:03d}"; names.append(name); allthys.append(f'"{SP}DCX_{s}.{name}"')
            js = list(range(SUB * k, SUB * k + SUB))
            lem = [f'lemma dc_{b}_{j:04d}: "dc_sub {bt} {j}"\n  {proof(f"dc_{b}_{j:04d}")}\n' for j in js]
            facts = " ".join(f"dc_{b}_{j:04d}" for j in js)
            sec = f'''lemma upt_{b}_{k:03d}: "[{js[0]}..<{js[-1] + 1}] = [{", ".join(map(str, js))}]"
  by (simp add: upt_rec)

lemma sec_{b}_{k:03d}: "\\<forall>j\\<in>{{16 * {k}..<16 * {k} + 16}}. dc_sub {bt} j"
proof
  fix j :: nat assume "j \\<in> {{16 * {k}..<16 * {k} + 16}}"
  then have "j \\<in> set [{js[0]}..<{js[-1] + 1}]" unfolding set_upt by simp
  then have "j \\<in> set [{", ".join(map(str, js))}]" unfolding upt_{b}_{k:03d} .
  then show "dc_sub {bt} j" using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
            w(f"{OUT}/S{s}/{name}.thy", f'theory {name}\n  imports "{SP}DC_Tables.DC_Tables"\nbegin\n\n' + "\n".join(lem) + "\n" + sec + "\nend\n")
    sess = f"{SP}DCX_{s}"
    root.append(f'session {sess} in "S{s}" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}DC_Tables\n  theories\n' + "".join(f"    {n}\n" for n in names))
    prev = sess
def old_lemma(b, t):
    facts = " ".join(f"dc_{b}_{k:03d}" for k in range(K0))
    return f'''lemma old_{b}: "k < {K0} \\<Longrightarrow> check_sector 53 dc_q 9 inv9_ivl ({t}) 20 (Float 1 (-26)) 100 (Float (int k) (-8)) (Float (int k + 1) (-8))"
proof -
  assume "k < {K0}"
  then have "k \\<in> set [0..<{K0}]" unfolding set_upt by simp
  then have "k \\<in> set [{", ".join(map(str, range(K0)))}]" unfolding upt_old .
  then show ?thesis using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
def new_lemma(b, t):
    facts = " ".join(f"sec_{b}_{k:03d}" for k in ks)
    return f'''lemma new_{b}: "{K0} \\<le> k \\<Longrightarrow> k < {K1} \\<Longrightarrow> \\<forall>j\\<in>{{16 * k..<16 * k + 16}}. dc_sub ({t}) j"
proof -
  assume "{K0} \\<le> k" "k < {K1}"
  then have "k \\<in> set [{K0}..<{K1}]" unfolding set_upt by simp
  then have "k \\<in> set [{", ".join(map(str, ks))}]" unfolding upt_new .
  then show ?thesis using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
final = f'''theory Double_Cross_Final
  imports "{SP}DC_Tables.DC_Split" {" ".join(old_thys)} {" ".join(allthys)}
begin

lemma upt_old: "[0..<{K0}] = [{", ".join(map(str, range(K0)))}]" by (simp add: upt_rec)

lemma upt_new: "[{K0}..<{K1}] = [{", ".join(map(str, ks))}]" by (simp add: upt_rec)

{old_lemma("c30", "Some (band30 53)")}
{old_lemma("nc", "None")}
{new_lemma("c30", "dc_b30")}
{new_lemma("nc", "None")}
text \\<open>The double cross stops within 20 corrections for every focus angle and every tie rule,
  with the 30-degree band and with no band.\\<close>

theorem double_cross_stops_band30:
  "tie_rule tm ts \\<Longrightarrow> stops_within dcp 9 (Some (pi / 6)) tm ts t 20"
  by (rule dc_split_terminates [OF band30_in [where p = 53, folded dc_b30_def] old_c30 [folded dc_b30_def] new_c30])

theorem double_cross_stops_no_band:
  "tie_rule tm ts \\<Longrightarrow> stops_within dcp 9 None tm ts t 20"
  by (rule dc_split_terminates [OF band_none old_nc new_nc])

ML \\<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles [@{{thm double_cross_stops_band30}}, @{{thm double_cross_stops_no_band}}])))\\<close>

end
'''
w(f"{OUT}/Final/Double_Cross_Final.thy", final)
root.append(f'session {SP}DCX_Final in "Final" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}DC_Tables {SP}DC_Sectors_0\n  theories\n    Double_Cross_Final\n')
w(f"{OUT}/ROOT", "\n".join(root))
print(len(allthys), "theories,", len(allthys) * SUB, "piece lemmas, sessions DC_Tables ..", prev, "DCX_Final")
