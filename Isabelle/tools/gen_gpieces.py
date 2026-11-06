"""Generate the check of the changed method (Guarantee_Checker) on the double cross (dc) or the
octagon (oc) as pieces [j/4096, (j+1)/4096], j < 3232, for the bands given.  Like gen_pieces.py.
usage: gen_gpieces.py dc|oc OUTDIR DMAX BANDS [mock]   (BANDS: nc, c30 or nc,c30)"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ARR = sys.argv[1]; OUT = os.path.abspath(sys.argv[2]); DMAX = sys.argv[3]; BANDSEL = sys.argv[4].split(",")
MOCK = len(sys.argv) > 5 and sys.argv[5] == "mock"
A = dict(dc=dict(T="GDC", t="gdc", X="GDCX", p="dcp", dlf="dc_dlf", parent="Guarantee_Checker", extra="",
                 fin="GDouble_Cross_Final", name="double_cross", desc="the double cross", log="gsector_progress.log",
                 guar="gdc_guarantee"),
         oc=dict(T="GOC", t="goc", X="GOCX", p="ocp", dlf="oc_dlf", parent="GDC_Tables", extra="",
                 fin="GOctagon_Final", name="octagon", desc="the octagon", log="goct_progress.log",
                 guar="goc_guarantee"))[ARR]
LOG = os.path.join(OUT, "progress.log") if MOCK else os.path.join(ROOT, "logs", A["log"])
NK, SUB, NSESS = 202, 16, 24
SP = "Mock" if MOCK else ""
allb = {"c30": A["t"] + "_b30", "nc": "None"}
bands = [(b, allb[b]) for b in BANDSEL]
def w(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True); open(path, "w").write(text)
def proof(name): return "sorry" if MOCK else f"by ({A['t']}_eval {name})"
qd = "quick_and_dirty, " if MOCK else ""
root = []
T, t, X = A["T"], A["t"], A["X"]
tables_in = open(f"{ROOT}/tools/{T}_Tables.thy.in").read().replace("@LOG@", LOG).replace("@DMAX@", DMAX)
if MOCK: tables_in = tables_in.replace('"GDC_Tables.GDC_Tables"', '"MockGDC_Tables.GDC_Tables"')
w(f"{OUT}/Tables/{T}_Tables.thy", tables_in)
w(f"{OUT}/Tables/{T}_Split.thy", f"theory {T}_Split\n  imports {T}_Tables\nbegin\n\n"
  + open(f"{ROOT}/tools/{T}_Split_body.in").read().replace("@DMAX@", DMAX) + "\nend\n")
par = A["parent"] if A["parent"] == "Guarantee_Checker" else SP + A["parent"]
root.append(f'session {SP}{T}_Tables in "Tables" = {par} +\n  options [{qd}timeout = 0]\n  theories\n    {T}_Tables\n    {T}_Split\n')
ks = list(range(NK)); prev = f"{SP}{T}_Tables"; allthys = []
for s in range(NSESS):
    mine = ks[s::NSESS]; names = []
    for k in mine:
        for b, bt in bands:
            name = f"{X}_{b}_{k:03d}"; names.append(name); allthys.append(f'"{SP}{X}_{s}.{name}"')
            js = list(range(SUB * k, SUB * k + SUB))
            lem = [f'lemma {t}_{b}_{j:04d}: "{t}_sub {bt} {j}"\n  {proof(f"{t}_{b}_{j:04d}")}\n' for j in js]
            facts = " ".join(f"{t}_{b}_{j:04d}" for j in js)
            sec = f'''lemma gupt_{b}_{k:03d}: "[{js[0]}..<{js[-1] + 1}] = [{", ".join(map(str, js))}]"
  by (simp add: upt_rec)

lemma gsec_{b}_{k:03d}: "\\<forall>j\\<in>{{16 * {k}..<16 * {k} + 16}}. {t}_sub {bt} j"
proof
  fix j :: nat assume "j \\<in> {{16 * {k}..<16 * {k} + 16}}"
  then have "j \\<in> set [{js[0]}..<{js[-1] + 1}]" unfolding set_upt by simp
  then have "j \\<in> set [{", ".join(map(str, js))}]" unfolding gupt_{b}_{k:03d} .
  then show "{t}_sub {bt} j" using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
            w(f"{OUT}/S{s}/{name}.thy", f'theory {name}\n  imports "{SP}{T}_Tables.{T}_Tables"\nbegin\n\n' + "\n".join(lem) + "\n" + sec + "\nend\n")
    sess = f"{SP}{X}_{s}"
    root.append(f'session {sess} in "S{s}" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}{T}_Tables\n  theories\n' + "".join(f"    {n}\n" for n in names))
    prev = sess
def all_lemma(b, tt):
    facts = " ".join(f"gsec_{b}_{k:03d}" for k in ks)
    return f'''lemma gall_{b}: "k < {NK} \\<Longrightarrow> \\<forall>j\\<in>{{16 * k..<16 * k + 16}}. {A['t']}_sub {tt} j"
proof -
  assume "k < {NK}"
  then have "k \\<in> set [0..<{NK}]" unfolding set_upt by simp
  then have "k \\<in> set [{", ".join(map(str, ks))}]" unfolding gupt_all .
  then show ?thesis using {facts}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed
'''
thms, names = [], []
for b, bt in bands:
    bdr, bin_ = ("None", "band_none") if b == "nc" else ("(Some (pi / 6))", f"band30_in [where p = 53, folded {t}_b30_def]")
    tag = "no_band" if b == "nc" else "band30"
    thms.append(f'''theorem g{A["name"]}_stops_{tag}:
  "tie_rule tm ts \\<Longrightarrow> gstops_within {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t {DMAX}"
  by (rule {t}_pieces_terminates [OF {bin_} gall_{b}])

theorem g{A["name"]}_sidelobes_{tag}:
  "tie_rule tm ts \\<Longrightarrow> \\<exists>n \\<le> {DMAX}. gelig {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) t = {{}} \\<and>
     (\\<forall>\\<phi>. pw {A["p"]} 9 (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) \\<phi> > sqmax {A["p"]} 9 (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) / 100 \\<longrightarrow>
        (\\<exists>q y. lift q y \\<and> (q = tm (fmains {A["p"]} 9 (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) t) mod M \\<or> (q < M \\<and> \\<not> in_band {bdr} t q))
           \\<and> (\\<forall>\\<theta>. min \\<phi> y \\<le> \\<theta> \\<and> \\<theta> \\<le> max \\<phi> y \\<longrightarrow>
                pw {A["p"]} 9 (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) \\<theta>
                  > sqmax {A["p"]} 9 (grun {A["p"]} 9 (real_of_float {A["dlf"]}) {bdr} tm ts t n) / 100 - 2 * real_of_float {A["dlf"]})))"
  by (rule {A["guar"]} [OF g{A["name"]}_stops_{tag}])
''')
    names += [f"g{A['name']}_stops_{tag}", f"g{A['name']}_sidelobes_{tag}"]
final = f'''theory {A["fin"]}
  imports "{SP}{T}_Tables.{T}_Split" {" ".join(allthys)}
begin

lemma gupt_all: "[0..<{NK}] = [{", ".join(map(str, ks))}]" by (simp add: upt_rec)

{"".join(all_lemma(b, t) for b, t in bands)}
text \\<open>The changed method stops on {A["desc"]} within {DMAX} corrections for every focus angle and
  every tie rule, and at the stop the true pattern is below -20 dB off the main lobe.\\<close>

{"".join(thms)}
ML \\<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles [{", ".join("@{thm " + n + "}" for n in names)}])))\\<close>

end
'''
w(f"{OUT}/Final/{A['fin']}.thy", final)
root.append(f'session {SP}{X}_Final in "Final" = {prev} +\n  options [{qd}timeout = 0]\n  sessions {SP}{T}_Tables\n  theories\n    {A["fin"]}\n')
w(f"{OUT}/ROOT", "\n".join(root))
print(len(allthys), "theories,", len(allthys) * SUB, "piece lemmas,", NSESS, "sessions, last", prev)
