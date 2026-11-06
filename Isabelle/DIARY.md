# Isabelle/HOL formalisation of the termination results — diary

Started 2026-11-03. Target: formalise exact_arithmetic_proofs.pdf (Parts A, B, C) in Isabelle2026.
Session Perturbative_Termination (parent HOL-Analysis). Check one theory: tools/chk.sh THEORY.

## Plan
1. Perturbative_Basics: steering vectors, patterns, grid, corrections, rows lemma, projection lemma, peaks.
2. Part A derivative/Taylor lemmas; circular distance; symmetry (double cross specific).
3. Interval model (HOL-Library.Interval_Float), Taylor cos/sin enclosure.
4. Checker (executable) + soundness; run by code generation.
5. Part C: certificate lemmas, Cholesky lemma, executable verification of F1-F4.

## Findings

## 2026-11-03
- Perturbative_Basics.thy green (Lemmas 2.1, 2.2, 2.6).
- Taylor_Enclosure.thy green (Lemmas 2.3, 2.4): proved via has_vector_derivative of complex-valued
  functions and has_derivative_inner; the sharp constant H = 2(D^2 + B E) comes out exactly as in the paper.
- Traps: `algebra` needs typed variables (generic sort fails silently); `simp add: abs_div_pos` loops;
  `has_field_derivative_def` uses `(*) D`, not `λh. h * D`; pgrep -f with a pattern that appears in the
  calling shell kills the shell (use `[p]attern` trick).
- Algorithm.thy green (Lemma 2.5, Definitions 1.1/1.2 as sets + run). Trap: metis with Max_in/Max_ge hangs; sel_nonempty proved by explicit Max_in/Max_ge steps.
- Interval_Model.thy and Node_Enclosure.thy green: complex intervals over HOL-Library.Interval_Float + HOL-Decision_Procs.Approximation_Bounds (verified cos, sqrt, pi; sin as cos(x-pi/2)); rows and curvature bounds enclosed. Trap: simp_all rewrites summands (r*(a *R z) -> -(…)) and breaks syntactic matches with interval definitions; prove element inclusions by intro with 'simp only: nth_map' instead. 'Hc' is a constant: don't reuse as a variable name.
- Sector_Bounds.thy green (E2, E3, E4: per-sector bounds on S, on neighbour differences, and on the circular
  distance via cdist = min(|w|, |w-2pi|, |w+2pi|) for |w| <= 2pi). Classify.thy drafted (index sets +
  soundness lemmas 5.1/5.2); checking it. Traps: `EX` and `term` are keywords/binders (parse errors look
  like hangs); `auto simp: PP_def` on big definitions runs for minutes (use `blast dest: PP_lt`);
  `by (simp ...) linarith` fails with "No subgoals" when simp finishes — use `(simp ...; linarith)`.
- Workflow: ROOT lists only green theories; the heap is rebuilt with -b after each; in-progress theories are
  checked as drafts against the heap (tools/chk.sh) so each check costs about a minute.
- Classify.thy and Search.thy green: the abstract interval checker is verified end to end (Lemmas 5.1, 5.2, Prop 6.2). Trap:  and  on goals mentioning the big set comprehensions can run for minutes — use explicit CollectI/imageE/mem_Collect_eq steps; context abbreviations export as global constants.
- Classify.thy and Search.thy green: the abstract interval checker is verified end to end (Lemmas 5.1, 5.2,
  Prop 6.2). Trap: obtain/simp on goals with the big set comprehensions can run for minutes; use explicit
  CollectI/imageE/mem_Collect_eq steps. Context abbreviations export as global constants (Classify.c).
- Executable version: the abstract `verify` recomputes rows and trig per use; the implementation must thread
  memoised lists (kernel, rows, curvature bounds, per-node c0) and be proved equal to `verify`.
- Exec_Node, Exec_Impl, Exec_Search green: executable list-based checker proved equal to the abstract one;
  check_sector_sound is the end-to-end theorem. Traps: `term` as a fact name is a keyword; exported context
  abbreviations (R, Hb, S, SQ, c, nd) clash with later variable names; `List.member` is now code-only.
- Executable performance: the library's float/interval code is slow (comparisons via rounded addition,
  rounding via a linear bitlen, pi recomputed per use). Fixed with proved code equations (Fast_Code.thy),
  exact complex arithmetic with rounding only at row storage, square-root-free curvature bound, memoised
  constants. A memoised constant defined through the routed function creates a cycle (silent hang).
- Symmetry.thy green (generic transport: a permutation of the elements, a bijection of the grid and an angle
  map with H1-H4 carry every tie rule's run across; all_rules_transport). Double_Cross_Symmetry.thy green:
  rotation by +-pi/2 and the diagonal reflection instantiated for the double cross (positions as exact
  dyadic floats), reduction of every real focus angle to [0, pi/4] (dc_stops_all), and
  double_cross_terminates: uniform sector checks [k 2^e, (k+1) 2^e], k < n, with n 2^e >= pi/4 give
  termination for every focus angle and every tie rule. Traps: presburger breaks down (or hangs) on nat
  goals with two `mod 1000`; use if-based grid maps and `by eval` over `\<forall>m<M`; simp turns the case
  `j = 1` into `j = Suc 0`, so position simp rules need a `Suc 0` variant; `c` is an exported abbreviation.
- Circular array (Part C) in Isabelle: Circular_Floor.thy green proves the certificate inequality (C.1),
  the norm bound from a Cholesky-type factor with an entrywise residual (C.2: (s2-delta)|c|^2 <= sum_Q |F|^2
  whenever row/column sums of |G - L L^T - s2 I| are <= delta; no singular values needed) and the floor
  theorem floor_from_certificates (maxAll c <= K maxQ c). Circular_Data.thy holds the certificates (both
  signs, weights rounded to 24-bit mantissas, so no reflection lemma is needed) and the double-precision
  Cholesky factors. Circular_Check.thy green: executable circ_check with circ_check_sound. Traps: simp on
  goals with [0..<64] or abs_interval unfolds everything and overflows the stack (use bspec and explicit
  nth equations); negative Float mantissas need parentheses in generated theory text.
- 2026-11-05 03:19: double-cross pieces build GREEN (BUILD EXIT 0, 10 h 15 min wall, 6,464 pieces, 404
  sectors, 0 failures). DCX_Final.Double_Cross_Final proves double_cross_stops_band30 and
  double_cross_stops_no_band: `tie_rule tm ts ⟹ stops_within dcp 9 band tm ts t 20`. Oracles:
  Code_Generator.holds (computation_check) and Code_Generator.holds_by_evaluation (eval), the two entry points
  of code-generator evaluation. Read theory output with `isabelle build_log -v -U -M oracles DCX_Final`.
- 2026-11-05 04:02: Hoare/ GREEN. Perturbative_Hoare.perturb_hoare is a total-correctness HOL-Hoare triple
  `[True] prog [Q]` for the MATLAB loop (no Max_iter; every grid scan a WHILE with variant M - k; outer
  variant D - n, n < D by busy_less). Assumes stops_within p N band tm ts t D; Q: w = run n, n <= D,
  m0 = tm (mains), every non-main peak outside the band <= -20 dB. No oracles. Double_Cross_Hoare:
  double_cross_hoare_band30 / _no_band (D = 20, assume tie_rule); oracles = code-generator evaluation only.
  Proof: `vcg_tc; (simp (no_asm) only: c0_lam corr_lam sq_patt)?; (clarsimp simp: scan_simps ...)?` and
  one rule for the exit VC. Traps: Classify's exported abbreviation `c` captures `c` in lemma statements
  (renamed w); simp turns k + 1 into Suc k and -20 < 10 * x into - 2 < x, so the scan invariants use
  opaque below/max_below/min_below/agrees with Suc lemmas, and the dB fold lemma is stated in the
  simplified form; clarsimp's hypsubst removes the program variables; linarith ran out of stack on a
  log iff (simp works); powr_minus + divide_inverse loops (use powr_neg_numeral); two sessions need two
  directories; a target session built without -b keeps no heap (DCX_Final rebuilt, 8 min).

## 2026-11-05 10:15 — UTP (ITree) triple replaces the HOL-Hoare one

- User wanted ITree/UTP-style triples (as in Verified Numerical Methods), not HOL-Hoare; HOL-Hoare
  theories deleted at the user's request (copy in the session scratchpad, removed_hol_hoare/).
- ITree_VCG ported to Isabelle2026: ~/Desktop/Academic/Isabelle_Stuff/IsabelleUTP_2026 (build.sh,
  PATCHES.md): upstream Optics/Z_Toolkit/Shallow_Expressions(+Z) + ITree stack, patched for the
  {verbose} Specification API, add_fun, del_proc, alethe_sko_ex'. AFP 2026 Optics lacks prism_matches.
- Hoare/ROOT: Perturbative_UTP_Base (ITree_VCG on Perturbative_Termination), Perturbative_UTP
  (Perturbative_Scans + Perturbative_UTP: programs scan/perturb/perturb_ann, perturb_ann_correct,
  perturb_correct; no oracles; vcg ~4.5 min), Double_Cross_UTP (double_cross_band30/no_band, n <= 20;
  oracles = code generator only; 6:43). Build: tools/build_utp.sh; jEdit: tools/jedit_utp.sh.
- Traps: literal_variables is on after ITree_VCG -> generic rule statements need
  [[literal_variables = false]]; vcg stops at `while ;; rest` -> rule thl_while_seq (prestate);
  unfold program defs, then simp only: prod.case kcomp_assoc before vcg; vcg's fun_eq_iff makes
  pointwise hyps -> simp only: fun_eq_iff [symmetric]; ITree `run` shadows ours (Algorithm.run);
  zstore needs default instances (real, complex, fun); field names become constants (no free n, k, w
  in later lemmas).

## 2026-11-05 10:43 — octagon pieces launched (near-octagon dropped by the user)

- Octagon defined with exact D4 symmetry (Pieces_Oct/Tables/Octagon_Symmetry.thy, ocd_q): axis +-a,
  a = double(0.0488); diagonal (+-b, +-b), b = double nearest a/sqrt 2 = 1243238886477031*2^-55; element
  order of the double cross; symmetry argument copied from Double_Cross_Symmetry (names *_oc / oc_*).
  checker/octagon.txt (old residues 1e-18) is NOT exactly symmetric, hence the new positions.
- C++ checker on octagon_d4.txt over [0,45]: CERTIFIED, D = 10, both bands, 80,681 nodes (DC 162,467).
- tools/gen_pieces_oct.py OUT D -> Pieces_Oct (OC_Tables = DC_Tables + Octagon_Symmetry/OC_Tables/OC_Split,
  OCX_0..23, OCX_Final: octagon_stops_band30/no_band, stops_within ocp 9 _ tm ts t 10). Mock (sorry) green.
- Real run: `isabelle build -d . -d Pieces -d Pieces_Oct -j 1 -o threads=10 -v OCX_Final`
  > logs/oct_pieces_build.log, progress logs/oct_progress.log, started 10:43; first pieces ~9 s.
- Trap: Double_Cross.thy already defines oc_q (old octagon) -> name clash; renamed ours ocd_q.
- 2026-11-05 15:59: octagon pieces build GREEN (BUILD EXIT 0, 5 h 17 min wall, 6,464 pieces, 0 failures).
  OCX_Final.Octagon_Final proves octagon_stops_band30 and octagon_stops_no_band:
  `tie_rule tm ts ⟹ stops_within ocp 9 band tm ts t 10`. Oracles: Code_Generator.holds,
  Code_Generator.holds_by_evaluation (same as the double cross). OCX_Final built without -b: no heap kept.

## 2026-11-05 — paper

- Proof/Paper_Termination/paper.tex (amsart, 22 pp): method, stopping condition, Theorems 1-4, proofs,
  listings copied verbatim by tools/extract_listings.py, figures by tools/make_figs.py. Proofread against
  the sources 14:10 (K bounds stated as 0.1614 K <= 1; verify splits unless exactly one candidate;
  reproduction commands need -b). Mosier reference still a placeholder (MosierTODO in refs.bib).
- 2026-11-05 16:15: Octagon_UTP GREEN (octagon_band30 / octagon_no_band: H[True] perturb (ocp, ...) [..., n <= 10, ...];
  oracles = code generator only; 6:05, plus 8:21 to rebuild OCX_Final, whose heap the -b-less build had not kept).
  Paper listings re-extracted: identical to the checked sources.

## 2026-11-05 — what the stop means (user question)
- NOT proved: "pattern below -20 dB everywhere at the stop". Only (I): strict grid peaks outside band, except m0.
- Simulation (scratchpad cont/cont_split*.py; 4501 foci in [0,pi/4] + bisection at sequence changes, 64x fine grid):
  - just outside the 30 deg band the stopped pattern is -4.5..-2.3 dB (DC), -4.0..-2.7 dB (oct): main lobe flank; (S) fails.
  - flat tops (two equal adjacent samples => no strict peak): DC 82 stops, missed sidelobe -20.0..-5.2 dB
    (t ~ 0.312 deg stops after 0 corrections at -5.2 dB); octagon 15 stops, -19.5..-15.2 dB.
  - between samples: DC 8 stops with true peak above -20 dB by <= 0.0004 dB; octagon none found.
- Paper: abstract, intro (method sentence, Hoare bullet, new "What stopping means" paragraph), §3 "The grid",
  new §3.4 "What the test does not see", §8 bullet, conclusion. Backup: scratchpad/paper_before_unseen.tex.
- Open: user to decide whether to change the test (count flat tops, margin or off-grid check) and prove the
  sidelobe guarantee.
- Proposed fix (not adopted yet): count the first point of a flat top as a peak, and lower the threshold by
  delta = H h^2/8, H = 2N^2(kR + 2k^2R^2) (|P''| bound from ||w|| <= sqrt N), DC: H = 4490, delta = 0.0222.
  Then stop => true pattern <= max/100 outside the main stretch +- one cell (run lemma + chord/parabola bound);
  general, no computation. Simulation (scratchpad cont/modified.py, DC no band, 6019 foci incl. 1518 at
  sequence changes): stops within 19, worst off-grid outside main lobe -20.195 dB, grid margin 0.19-0.34 dB.

- Paper §3.4 numbers (original method): tools/sim/flat_tops.py dc|oct (recreated; the scratchpad copy is gone).
