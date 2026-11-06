"""Copy Isabelle text verbatim from the theory sources into listings/*.thy for \\lstinputlisting.
Each snippet is a top-level command (or a range of them) taken from the checked sources; 'stmt'
keeps only the statement of a lemma.  Prints the Isabelle symbols used, to check the listings style."""
import os, re, sys
I = os.path.expanduser("~/Desktop/Matlab_UH_Project/Proof/Isabelle")
OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "listings")
TOP = re.compile(r"^(definition|lemma|theorem|corollary|lemmas|primrec|fun|function|abbreviation|text|section|subsection|"
                 r"end|zstore|program|ML|declare|instantiation|lemma_def|context|method_setup|record|datatype)\b")
PROOF = re.compile(r"^\s*(proof|by|apply|unfolding|using|done)\b")

def block(path, start, mode="full", until=None, strip_text=True):
    L = open(os.path.join(I, path), encoding="utf-8").read().split("\n")
    i = next(k for k, l in enumerate(L) if re.match(start, l))
    j = i + 1
    while j < len(L):
        l = L[j]
        if until is not None:
            if re.match(until, l): break
        elif TOP.match(l): break
        j += 1
    out = L[i:j]
    if strip_text:  # drop text blocks inside a range
        res, skip = [], False
        for l in out:
            if re.match(r"^text\b", l): skip = not l.rstrip().endswith("\\<close>")
            elif skip: skip = not l.rstrip().endswith("\\<close>")
            else: res.append(l)
        out = res
    if mode == "stmt":
        k = next((n for n, l in enumerate(out) if n > 0 and PROOF.match(l)), len(out))
        out = out[:k]
    while out and not out[-1].strip(): out.pop()
    return "\n".join(out) + "\n"

S = {
 "basics": ("Perturbative_Basics.thy", r"^definition kw", "full", r"^lemma cmod_steer"),
 "corr_null": ("Perturbative_Basics.thy", r"^lemma patt_corr_self", "stmt", None),
 "rows": ("Perturbative_Basics.thy", r"^primrec rows", "full", r"^lemma patt_corr:"),
 "rows_lemma": ("Perturbative_Basics.thy", r"^lemma patt_exc_rows", "stmt", None),
 "peaks": ("Perturbative_Basics.thy", r"^definition prev_idx", "full", r"^lemma prev_next"),
 "algorithm": ("Algorithm.thy", r"^definition sqmax", "full", r"^text \\<open>The corrected indices"),
 "run_exc": ("Algorithm.thy", r"^lemma run_exc", "full", None),
 "cdist": ("Algorithm.thy", r"^definition cdist", "full", None),
 "taylor": ("Taylor_Enclosure.thy", r"^theorem SS_taylor", "stmt", None),
 "hc": ("Taylor_Enclosure.thy", r"^definition Bc", "full", r"^lemma norm_FF:"),
 "ss": ("Taylor_Enclosure.thy", r"^definition SS ", "full", r"^definition SS1"),
 "sq_rows": ("Taylor_Enclosure.thy", r"^lemma sq_exc_SS", "stmt", None),
 "classify": ("Classify.thy", r"^definition PP", "full", r"^section"),
 "terminal_sound": ("Classify.thy", r"^lemma terminal_sound", "stmt", None),
 "sel_cand": ("Classify.thy", r"^lemma sel_cand", "stmt", None),
 "verify": ("Search.thy", r"^fun verify", "full", None),
 "verify_sound": ("Search.thy", r"^theorem verify_sound", "stmt", None),
 "check_sector": ("Exec_Search.thy", r"^definition check_sector", "full", None),
 "check_sector_sound": ("Exec_Search.thy", r"^theorem check_sector_sound", "stmt", None),
 "dc_pos": ("Double_Cross.thy", r"^definition double_cross_pos", "full", None),
 "dc_stops": ("Double_Cross_Symmetry.thy", r"^definition dc_stops", "full", None),
 "dc_stops_all": ("Double_Cross_Symmetry.thy", r"^theorem dc_stops_all", "stmt", None),
 "transport": ("Symmetry.thy", r"^theorem all_rules_transport", "stmt", None),
 "dc_sub": ("Pieces/Tables/DC_Tables.thy", r"^definition dc_sub", "full", None),
 "dc_piece": ("Pieces/S0/DCX_c30_000.thy", r"^lemma dc_c30_0000", "full", None),
 "dc_final": ("Pieces/Final/Double_Cross_Final.thy", r"^theorem double_cross_stops_band30", "full", r"^ML"),
 "circ_defs": ("Circular_Floor.thy", r"^definition rc", "full", r"^lemma Qset_subset"),
 "circ_maxq": ("Circular_Floor.thy", r"^definition maxQ", "full", r"^lemma maxQ_ge"),
 "circ_cert": ("Circular_Floor.thy", r"^definition certificate", "full", None),
 "circ_floor_thm": ("Circular_Floor.thy", r"^theorem floor_from_certificates", "stmt", None),
 "circ_result": ("Circular_Result.thy", r"^theorem circular_floor_20", "full", r"^end"),
 "utp_seq": ("Hoare/UTP/Perturbative_UTP.thy", r"^lemma thl_while_seq", "stmt", None),
 "utp_store": ("Hoare/UTP/Perturbative_UTP.thy", r"^zstore pstate", "full", None),
 "utp_scan": ("Hoare/UTP/Perturbative_UTP.thy", r"^program scan", "full", None),
 "utp_perturb": ("Hoare/UTP/Perturbative_UTP.thy", r"^program perturb ", "full", None),
 "utp_perturb_ann": ("Hoare/UTP/Perturbative_UTP.thy", r"^program perturb_ann", "full", None),
 "utp_ann_eq": ("Hoare/UTP/Perturbative_UTP.thy", r"^lemma perturb_ann_is_perturb", "full", None),
 "utp_correct": ("Hoare/UTP/Perturbative_UTP.thy", r"^theorem perturb_ann_correct", "full", None),
 "utp_corollary": ("Hoare/UTP/Perturbative_UTP.thy", r"^corollary perturb_correct", "full", None),
 "utp_dc": ("Hoare/UTP/Double_Cross/Double_Cross_UTP.thy", r"^theorem double_cross_band30", "full", None),
 "utp_busy": ("Hoare/UTP/Perturbative_Scans.thy", r"^lemma busy_less", "stmt", None),
 "oc_final": ("Pieces_Oct/Final/Octagon_Final.thy", r"^theorem octagon_stops_band30", "full", r"^ML"),
 "oc_pos": ("Pieces_Oct/Tables/Octagon_Symmetry.thy", r"^definition octagon_d4_pos", "full", None),
 "utp_oc": ("Hoare/UTP/Octagon/Octagon_UTP.thy", r"^theorem octagon_band30", "full", None),
 "utp_below": ("Hoare/UTP/Perturbative_Scans.thy", r"^definition below", "full", r"^lemma finite_below"),
 "g_method": ("Guarantee/G_Method.thy", r"^definition is_fpeak", "full", r"^definition gstops_within"),
 "g_chord": ("Guarantee/G_Chord.thy", r"^theorem chord_max", "stmt", None),
 "g_pw": ("Guarantee/G_Pattern.thy", r"^definition pw", "full", None),
 "g_cell": ("Guarantee/G_Pattern.thy", r"^theorem pw_cell_max", "stmt", None),
 "g_nrm": ("Guarantee/G_Pattern.thy", r"^lemma nrm_corr", "stmt", None),
 "g_hc": ("Guarantee/G_Pattern.thy", r"^theorem Hc_le_norm", "stmt", None),
 "g_walk": ("Guarantee/G_Discrete.thy", r"^theorem walk_to_main", "stmt", None),
 "g_guarantee": ("Guarantee/G_Guarantee.thy", r"^theorem guarantee_at_stop", "stmt", None),
 "g_no_band": ("Guarantee/G_Guarantee.thy", r"^corollary guarantee_no_band", "stmt", None),
 "g_run": ("Guarantee/G_Guarantee.thy", r"^theorem gstops_guarantee", "stmt", None),
 "gc_classify": ("GChecker/GC_Classify.thy", r"^definition PPg", "full", r"^lemma PPg_lt"),
 "gc_check": ("GChecker/GC_Exec.thy", r"^theorem gcheck_sector_sound", "stmt", None),
 "gc_transport": ("GChecker/GC_Symmetry.thy", r"^theorem gall_rules_transport", "stmt", None),
 "gdc_gam": ("GChecker/GC_Double_Cross.thy", r"^lemma dc_gam", "stmt", None),
 "gdc_dl": ("GChecker/GC_Double_Cross.thy", r"^lemma dc_dl_ok", "stmt", None),
 "gdc_final": ("Pieces_G/Final/GDouble_Cross_Final.thy", r"^theorem gdouble_cross_stops_no_band", "full", r"^ML"),
 "goc_final": ("Pieces_GOct/Final/GOctagon_Final.thy", r"^theorem goctagon_stops_no_band", "full", r"^theorem goctagon_sidelobes_no_band"),
}
syms = set()
for name, (path, start, mode, until) in S.items():
    txt = block(path, start, mode, until)
    syms |= set(re.findall(r"\\<[^>]*>", txt))
    open(os.path.join(OUT, name + ".thy"), "w", encoding="utf-8").write(txt)
print(len(S), "listings;", "symbols:", " ".join(sorted(syms)))
