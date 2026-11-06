"""Generate the sector-check sessions for the double cross.
Sectors [k/256, (k+1)/256] rad, k < 202 (202/256 >= pi/4), for the 30-degree band and for no band.
Chunks of CHUNK sectors form one theory; NSESS chained sessions give checkpoints.
Each check logs its start and end to logs/sector_progress.log.  usage: gen_sectors.py [OUTDIR]"""
import os, math, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.join(ROOT, "Sectors")
LOG = os.path.join(ROOT, "logs", "sector_progress.log")
N, E, CHUNK, NSESS = 202, -8, 8, 13
assert N * 2.0**E >= math.pi / 4
bands = [("c30", "Some (band30 53)"), ("nc", "None")]
jobs = [(b, k) for k in range(N) for b in bands]          # interleave so each session mixes both bands
chunks = [jobs[i:i + CHUNK] for i in range(0, len(jobs), CHUNK)]
per = math.ceil(len(chunks) / NSESS)
os.makedirs(os.path.join(OUT, "Progress"), exist_ok=True)
tmpl = open(os.path.join(ROOT, "tools", "Sector_Progress.thy.in")).read()
open(os.path.join(OUT, "Progress", "Sector_Progress.thy"), "w").write(tmpl.replace("@LOG@", LOG))
root_lines, prev = ['session DC_Progress in "Progress" = Perturbative_Termination +\n  theories\n    Sector_Progress\n'], "DC_Progress"
for s in range(NSESS):
    mine = chunks[s * per:(s + 1) * per]
    names = []
    for ci, ch in enumerate(mine):
        name = f"DCS_{s}_{ci:02d}"; names.append(name)
        lem = []
        for (bname, bterm), k in ch:
            lem.append(f'lemma dc_{bname}_{k:03d}: "check_sector 53 dc_q 9 inv9_ivl ({bterm}) 20 (Float 1 (-26)) 100 (Float (int {k}) ({E})) (Float (int {k} + 1) ({E}))"\n  by (progress_eval dc_{bname}_{k:03d})\n')
        imports = '"Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code" "DC_Progress.Sector_Progress"'
        os.makedirs(os.path.join(OUT, f"S{s}"), exist_ok=True)
        open(os.path.join(OUT, f"S{s}", name + ".thy"), "w").write(
            f"theory {name}\n  imports {imports}\nbegin\n\n" + "\n".join(lem) + "\nend\n")
    sess = f"DC_Sectors_{s}"
    root_lines.append(f'session {sess} in "S{s}" = {prev} +\n  options [timeout = 0]\n  sessions Perturbative_Termination\n  theories\n' +
                      "".join(f"    {n}\n" for n in names))
    prev = sess

os.makedirs(os.path.join(OUT, "Final"), exist_ok=True)
allthys = []
for s_ in range(NSESS):
    for ci in range(len(chunks[s_ * per:(s_ + 1) * per])):
        allthys.append(f'"DC_Sectors_{s_}.DCS_{s_}_{ci:02d}"')
lst = ", ".join(str(k) for k in range(N))
def facts(b): return " ".join(f"dc_{b}_{k:03d}" for k in range(N))
final = f"""theory Double_Cross_Final
  imports "Perturbative_Termination.Double_Cross_Symmetry" {" ".join(allthys)}
begin

lemma upt_N: "[0..<{N}] = [{lst}]" by eval

lemma sectors_c30: "k < {N} \\<Longrightarrow> check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int k) ({E})) (Float (int k + 1) ({E}))"
proof -
  assume "k < {N}"
  then have "k \\<in> set [0..<{N}]" by simp
  then have "k \\<in> set [{lst}]" by (simp only: upt_N)
  then show ?thesis using {facts("c30")}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

lemma sectors_nc: "k < {N} \\<Longrightarrow> check_sector 53 dc_q 9 inv9_ivl None 20 (Float 1 (-26)) 100 (Float (int k) ({E})) (Float (int k + 1) ({E}))"
proof -
  assume "k < {N}"
  then have "k \\<in> set [0..<{N}]" by simp
  then have "k \\<in> set [{lst}]" by (simp only: upt_N)
  then show ?thesis using {facts("nc")}
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

lemma cover: "pi / 4 \\<le> real_of_float (Float (int {N}) ({E}))"
proof -
  have "real_of_float (Float (int {N}) ({E})) = {N} / {2**(-E)}" by (simp add: powr_minus_divide)
  moreover have "pi \\<le> 3.1416" using pi_approx by simp
  ultimately show ?thesis by simp
qed

text \\<open>The double cross stops within 20 corrections for every focus angle and every tie rule,
  with the 30-degree band and with no band.\\<close>

theorem double_cross_stops_band30:
  "tie_rule tm ts \\<Longrightarrow> stops_within dcp 9 (Some (pi / 6)) tm ts t 20"
  by (rule double_cross_terminates [OF band30_in _ cover sectors_c30]) simp_all

theorem double_cross_stops_no_band:
  "tie_rule tm ts \\<Longrightarrow> stops_within dcp 9 None tm ts t 20"
  by (rule double_cross_terminates [OF band_none _ cover sectors_nc]) simp_all

end
"""
open(os.path.join(OUT, "Final", "Double_Cross_Final.thy"), "w").write(final.replace("\\\\", "\\"))
root_lines.append(f'session DC_Final in "Final" = {prev} +\n  sessions Perturbative_Termination\n  theories\n    Double_Cross_Final\n')
open(os.path.join(OUT, "ROOT"), "w").write("\n".join(root_lines))
print(len(jobs), "sector checks in", len(chunks), "theories,", NSESS, "sessions; last session", prev)
