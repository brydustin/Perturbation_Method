theory DC_Tables
  imports "Perturbative_Termination.Double_Cross_Symmetry" "Perturbative_Termination.Fast_Code"
begin

text \<open>Sector checks on pieces \<open>[j 2\<^sup>-\<^sup>1\<^sup>2, (j+1) 2\<^sup>-\<^sup>1\<^sup>2]\<close>. The kernel and bound tables depend only on
  the array, so the checker is compiled once and computes them once.\<close>

definition dc_kl :: "civ list list" where "dc_kl = kernelL 53 dc_q 9"
definition dc_gl :: "float interval list" where "dc_gl = gridLst 53"
definition dc_hb :: "float list" where "dc_hb = hbL 53 dc_q 9 dc_kl"
definition dc_b30 :: "float interval option" where "dc_b30 = Some (band30 53)"

definition dc_sub :: "float interval option \<Rightarrow> nat \<Rightarrow> bool" where
  "dc_sub band j = check_sector 53 dc_q 9 inv9_ivl band 20 (Float 1 (-26)) 100 (Float (int j) (-12)) (Float (int j + 1) (-12))"

lemma dc_sub_code [code]:
  "dc_sub band j = verify_impl 53 dc_q 9 inv9_ivl dc_kl dc_gl band 20 (Float 1 (-26)) 100
     (Float (int j) (-12)) (Float (int j + 1) (-12)) [] dc_kl dc_hb"
  by (simp only: dc_sub_def check_sector_def dc_kl_def dc_gl_def dc_hb_def Let_def)

text \<open>A piece of width \<open>2\<^sup>-\<^sup>3\<^sup>0\<close>, only for timing the checker.\<close>
definition dc_tiny :: "nat \<Rightarrow> bool" where
  "dc_tiny j = verify_impl 53 dc_q 9 inv9_ivl dc_kl dc_gl dc_b30 20 (Float 1 (-26)) 100
     (Float (int j) (-30)) (Float (int j + 1) (-30)) [] dc_kl dc_hb"

text \<open>\<open>dc_eval x\<close> proves \<open>dc_sub b j\<close> with the compiled checker and logs start and end of \<open>x\<close>.\<close>
ML \<open>
val dc_check = @{computation_check terms: Trueprop dc_sub dc_tiny dc_b30 "None :: float interval option"
  "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc}
val progress_seen = Synchronized.var "progress_seen" (Symtab.empty: unit Symtab.table)
fun progress_write line =
  File.append (Path.explode "/home/dusty/Desktop/Matlab_UH_Project/Proof/Isabelle/logs/sector_progress.log")
    (Date.fmt "%Y-%m-%d %H:%M:%S" (Date.fromTimeLocal (Time.now ())) ^ "  " ^ line ^ "\n")
fun progress_once name =
  if Synchronized.change_result progress_seen (fn tab =>
       if Symtab.defined tab name then (false, tab) else (true, Symtab.update (name, ()) tab))
  then progress_write ("started  " ^ name) else ()
\<close>
method_setup dc_eval = \<open>Scan.lift Parse.name >> (fn name => fn ctxt =>
  let
    fun tac i = CONVERSION (dc_check ctxt) i THEN resolve_tac ctxt [TrueI] i
    fun secs t = Real.fmt (StringCvt.FIX (SOME 0)) (Time.toReal (#elapsed (Timing.result t)))
  in
    SIMPLE_METHOD' (fn i => fn st => Seq.make (fn () =>
      let val _ = progress_once name; val t = Timing.start ()
      in case Seq.pull (tac i st) of
           NONE => (if Time.toReal (#elapsed (Timing.result t)) >= 1.0
                    then progress_write ("FAILED   " ^ name ^ " after " ^ secs t ^ " s") else (); NONE)
         | SOME (st', _) => (progress_write ("finished " ^ name ^ " in " ^ secs t ^ " s"); SOME (st', Seq.empty))
      end))
  end)\<close> "compiled sector check with progress logging"

end
