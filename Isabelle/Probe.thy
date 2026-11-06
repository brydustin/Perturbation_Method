theory Probe
  imports Double_Cross Fast_Code
begin

definition probe_kernel :: "unit \<Rightarrow> civ list list" where "probe_kernel u = kernelL 53 dc_q 9"
definition pr_c0 :: "unit \<Rightarrow> civ list" where "pr_c0 u = c0L 53 dc_q 9 (interval_of (tc (Float 0 0) (Float 1 (-12))))"
definition pr_c0p :: "unit \<Rightarrow> civ list" where "pr_c0p u = c0pL 53 dc_q 9 (interval_of (tc (Float 0 0) (Float 1 (-12))))"
definition pr_sq :: "civ list list \<Rightarrow> civ list \<Rightarrow> float interval list" where "pr_sq kl CL = sqL 53 9 kl CL"
definition pr_s1 :: "civ list list \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> float interval list" where "pr_s1 kl CL CPL = s1L 53 9 kl CL CPL"
definition pr_rad :: "float interval list \<Rightarrow> float list \<Rightarrow> float list" where "pr_rad Ds hl = radL 53 Ds hl (Float 0 0) (Float 1 (-12))"
definition pr_diff :: "float interval list \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float interval list" where
  "pr_diff Qs Ds hl = diffL 53 prev_idx Qs Ds hl (Float 0 0) (Float 1 (-12))"
definition pr_cd :: "unit \<Rightarrow> float interval list" where
  "pr_cd u = (let gl = gridLst 53 in cdL 53 gl (Float 0 0) (Float 1 (-12)) (n0I gl (Float 0 0) (Float 1 (-12))))"
definition pr_gcol :: "civ list list \<Rightarrow> civ list" where "pr_gcol kl = gcolL 53 9 inv9_ivl kl 500"
definition pr_step_noround :: "civ list list \<Rightarrow> civ list \<Rightarrow> civ list list" where
  "pr_step_noround rl g = map (\<lambda>m. map (\<lambda>j. csub 53 (rl ! m ! j) (cmul 53 (g ! m) (rl ! 500 ! j))) [0..<9]) [0..<M]"
definition pr_round :: "civ list list \<Rightarrow> civ list list" where
  "pr_round rl = map (\<lambda>row. map (cround 53) row) rl"
definition probe_hb :: "civ list list \<Rightarrow> float list" where "probe_hb kl = hbL 53 dc_q 9 kl"

ML \<open>
fun timed name f =
  let val t = Timing.start (); val r = f () in
    writeln (name ^ ": " ^ Timing.message (Timing.result t)); r end;
val kl = timed "kernel table" (fn () => @{code probe_kernel} ());
val hl = timed "curvature table" (fn () => @{code probe_hb} kl);
val c0l = timed "c0L" (fn () => @{code pr_c0} ());
val c0pl = timed "c0pL" (fn () => @{code pr_c0p} ());
val qs = timed "sqL" (fn () => @{code pr_sq} kl c0l);
val ds = timed "s1L" (fn () => @{code pr_s1} kl c0l c0pl);
val rd = timed "radL" (fn () => @{code pr_rad} ds hl);
val _ = timed "diffL" (fn () => @{code pr_diff} qs ds hl);
val _ = timed "cdL" (fn () => @{code pr_cd} ());
val gc = timed "gcolL" (fn () => @{code pr_gcol} kl);
val st = timed "step without rounding" (fn () => @{code pr_step_noround} kl gc);
val _ = timed "rounding of rows" (fn () => @{code pr_round} st);
\<close>

end
