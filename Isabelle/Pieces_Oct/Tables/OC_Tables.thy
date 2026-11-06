theory OC_Tables
  imports "DC_Tables.DC_Tables" Octagon_Symmetry
begin

text \<open>The octagon's sector checks on pieces \<open>[j 2\<^sup>-\<^sup>1\<^sup>2, (j+1) 2\<^sup>-\<^sup>1\<^sup>2]\<close>, as in DC_Tables (whose shift-based code
  equations are inherited).\<close>

definition oc_kl :: "civ list list" where "oc_kl = kernelL 53 ocd_q 9"
definition oc_gl :: "float interval list" where "oc_gl = gridLst 53"
definition oc_hb :: "float list" where "oc_hb = hbL 53 ocd_q 9 oc_kl"
definition oc_b30 :: "float interval option" where "oc_b30 = Some (band30 53)"

definition oc_sub :: "float interval option \<Rightarrow> nat \<Rightarrow> bool" where
  "oc_sub band j = check_sector 53 ocd_q 9 inv9_ivl band 10 (Float 1 (-26)) 100 (Float (int j) (-12)) (Float (int j + 1) (-12))"

lemma oc_sub_code [code]:
  "oc_sub band j = verify_impl 53 ocd_q 9 inv9_ivl oc_kl oc_gl band 10 (Float 1 (-26)) 100
     (Float (int j) (-12)) (Float (int j + 1) (-12)) [] oc_kl oc_hb"
  by (simp only: oc_sub_def check_sector_def oc_kl_def oc_gl_def oc_hb_def Let_def)

text \<open>A piece of width \<open>2\<^sup>-\<^sup>3\<^sup>0\<close>, only for timing the checker.\<close>
definition oc_tiny :: "nat \<Rightarrow> bool" where
  "oc_tiny j = verify_impl 53 ocd_q 9 inv9_ivl oc_kl oc_gl oc_b30 10 (Float 1 (-26)) 100
     (Float (int j) (-30)) (Float (int j + 1) (-30)) [] oc_kl oc_hb"

text \<open>\<open>oc_eval x\<close> proves \<open>oc_sub b j\<close> with the compiled checker and logs start and end of \<open>x\<close>.\<close>
ML \<open>
val oc_check = @{computation_check terms: Trueprop oc_sub oc_tiny oc_b30 "None :: float interval option"
  "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc}
val oc_progress_seen = Synchronized.var "oc_progress_seen" (Symtab.empty: unit Symtab.table)
fun oc_progress_write line =
  File.append (Path.explode "/home/dusty/Desktop/Matlab_UH_Project/Proof/Isabelle/logs/oct_progress.log")
    (Date.fmt "%Y-%m-%d %H:%M:%S" (Date.fromTimeLocal (Time.now ())) ^ "  " ^ line ^ "\n")
fun oc_progress_once name =
  if Synchronized.change_result oc_progress_seen (fn tab =>
       if Symtab.defined tab name then (false, tab) else (true, Symtab.update (name, ()) tab))
  then oc_progress_write ("started  " ^ name) else ()
\<close>
method_setup oc_eval = \<open>Scan.lift Parse.name >> (fn name => fn ctxt =>
  let
    fun tac i = CONVERSION (oc_check ctxt) i THEN resolve_tac ctxt [TrueI] i
    fun secs t = Real.fmt (StringCvt.FIX (SOME 0)) (Time.toReal (#elapsed (Timing.result t)))
  in
    SIMPLE_METHOD' (fn i => fn st => Seq.make (fn () =>
      let val _ = oc_progress_once name; val t = Timing.start ()
      in case Seq.pull (tac i st) of
           NONE => (if Time.toReal (#elapsed (Timing.result t)) >= 1.0
                    then oc_progress_write ("FAILED   " ^ name ^ " after " ^ secs t ^ " s") else (); NONE)
         | SOME (st', _) => (oc_progress_write ("finished " ^ name ^ " in " ^ secs t ^ " s"); SOME (st', Seq.empty))
      end))
  end)\<close> "compiled sector check with progress logging"

end
