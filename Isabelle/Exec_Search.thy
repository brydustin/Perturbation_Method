theory Exec_Search
  imports Exec_Impl
begin

section \<open>Global tables and the row state\<close>

definition kernelL :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> civ list list" where
  "kernelL p q N = map (\<lambda>m. map (\<lambda>j. kernel_ivl p q m j) [0..<N]) [0..<M]"

definition gridLst :: "nat \<Rightarrow> float interval list" where
  "gridLst p = map (grid_ivl p) [0..<M]"

lemma gridLst_nth: "m < M \<Longrightarrow> gridLst p ! m = grid_ivl p m"
  by (simp add: gridLst_def)

text \<open>Invariants of the tables.\<close>
definition kernel_inv :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> civ list list \<Rightarrow> bool" where
  "kernel_inv p q N kl \<longleftrightarrow> length kl = M \<and> (\<forall>m < M. length (kl ! m) = N \<and> (\<forall>j < N. kl ! m ! j = kernel_ivl p q m j))"

lemma kernel_inv_kernelL: "kernel_inv p q N (kernelL p q N)"
  by (simp add: kernel_inv_def kernelL_def)

definition rows_inv :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat list \<Rightarrow> civ list list \<Rightarrow> bool" where
  "rows_inv p q N IN \<sigma> rl \<longleftrightarrow> length rl = M \<and> (\<forall>m < M. length (rl ! m) = N \<and> (\<forall>j < N. rl ! m ! j = rows_ivl p q N IN \<sigma> m j))"

lemma rows_inv_init: "rows_inv p q N IN [] (kernelL p q N)"
  by (simp add: rows_inv_def kernelL_def)

text \<open>The Gram column of \<open>s\<close> and the row update.\<close>
definition gcolL :: "nat \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list list \<Rightarrow> nat \<Rightarrow> civ list" where
  "gcolL p N IN kl s = map (\<lambda>m. cround p (cscale p IN (csum p (map (\<lambda>j. cmul p (kl ! m ! j) (ccnj (kl ! s ! j))) [0..<N])))) [0..<M]"

lemma gcolL_nth:
  assumes "kernel_inv p q N kl" "m < M" "s < M"
  shows "gcolL p N IN kl s ! m = cround p (gram_ivl p q N IN m s)"
  unfolding gcolL_def gram_ivl_def using assms
  by (simp add: kernel_inv_def) (intro arg_cong [where f = "cround p"] arg_cong [where f = "cscale p IN"] arg_cong [where f = "csum p"] map_upt_cong; simp)

definition stepL :: "nat \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list list \<Rightarrow> civ list list \<Rightarrow> nat \<Rightarrow> civ list list" where
  "stepL p N IN kl rl s = (let g = gcolL p N IN kl s in
     map (\<lambda>m. map (\<lambda>j. cround p (csub p (rl ! m ! j) (cmul p (g ! m) (rl ! s ! j)))) [0..<N]) [0..<M])"

lemma rows_inv_step:
  assumes k: "kernel_inv p q N kl" and r: "rows_inv p q N IN \<sigma> rl" and s: "s < M"
  shows "rows_inv p q N IN (s # \<sigma>) (stepL p N IN kl rl s)"
  unfolding rows_inv_def stepL_def Let_def using r s
  by (simp add: rows_inv_def gcolL_nth [OF k _ s])

definition hbL :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> civ list list \<Rightarrow> float list" where
  "hbL p q N rl = (let GL = gamL p q N in map (\<lambda>m. upper (Hc_ivlG p N (Rf rl m) GL)) [0..<M])"

lemma hbL_nth: "m < M \<Longrightarrow> hbL p q N rl ! m = upper (Hc_ivl p q N (Rf rl m))"
  by (simp add: hbL_def Let_def Hc_ivlG_eq)

lemma agree_state:
  assumes r: "rows_inv p q N IN \<sigma> rl"
  shows "agree N (Rf rl) (Hbf (hbL p q N rl)) (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>)"
proof -
  have R: "\<And>m j. m < M \<Longrightarrow> j < N \<Longrightarrow> Rf rl m j = Rref p q N IN \<sigma> m j"
    using r by (simp add: rows_inv_def Rf_def Rref_def)
  have H: "\<And>m. m < M \<Longrightarrow> Hbf (hbL p q N rl) m = Hbref p q N IN \<sigma> m"
    unfolding Hbf_def Hbref_def using R by (simp add: Rref_def hbL_nth) (intro arg_cong [where f = upper] Hc_ivl_cong; simp)
  show ?thesis unfolding agree_def using R H by simp
qed

section \<open>The executable search\<close>

definition all_okI :: "nat \<Rightarrow> float interval list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> bool" where
  "all_okI p gridL lo hi n0 \<longleftrightarrow> list_all (\<lambda>m. upper (abs_interval (w_ivl p (gridL ! m) (tc lo hi) (n0 m))) \<le> lower (twopi_ivl p)) [0..<M]"

lemma all_okI_eq: "(\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m) \<Longrightarrow> all_okI p gridL lo hi n0 = all_ok p lo hi n0"
  unfolding all_okI_def all_ok_def dist_ok_def list_all_iff set_upt by auto

text \<open>The integer of the distance reduction: the nearest integer to \<open>(\<phi>\<^sub>m - t\<^sub>c)/(2\<pi>)\<close>, computed in floats;
  any integer would be sound.\<close>
definition n0I :: "float interval list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> int" where
  "n0I gridL lo hi m = int_floor_fl ((lower (gridL ! m) - tc lo hi) * Float 5734161139222659 (-55) + Float 1 (-1))"

fun verify_impl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list list \<Rightarrow> float interval list \<Rightarrow>
                    float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat list \<Rightarrow> civ list list \<Rightarrow> float list \<Rightarrow> bool" where
  "verify_impl p q N IN kl gridL band Dmax wmin 0 lo hi \<sigma> rl hl = False"
| "verify_impl p q N IN kl gridL band Dmax wmin (Suc f) lo hi \<sigma> rl hl =
     (let n0 = n0I gridL lo hi in
      if \<not> all_okI p gridL lo hi n0 then False
      else let nd = node_impl p q N gridL n0 lo hi rl hl in
        if terminalI p band nd then True
        else let K = candsI p band nd in
          if (length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo
            then verify_impl p q N IN kl gridL band Dmax wmin f lo (tc lo hi) \<sigma> rl hl
               \<and> verify_impl p q N IN kl gridL band Dmax wmin f (tc lo hi) hi \<sigma> rl hl
          else if K = [] then True
          else if Dmax \<le> length \<sigma> then False
          else list_all (\<lambda>s. let rl' = stepL p N IN kl rl s in
                               verify_impl p q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) rl' (hbL p q N rl')) K)"

section \<open>Equivalence with the abstract search\<close>

lemma cands_lt: "s \<in> set (cands p q N RR HH lo hi n0 band) \<Longrightarrow> s < M"
  by (simp add: cands_def)

theorem verify_impl_eq:
  assumes k: "kernel_inv p q N kl" and g: "\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m"
  shows "rows_inv p q N IN \<sigma> rl \<Longrightarrow>
         verify_impl p q N IN kl gridL band Dmax wmin f lo hi \<sigma> rl (hbL p q N rl)
         = verify p q N IN (n0I gridL) band Dmax wmin f lo hi \<sigma>"
proof (induction f arbitrary: lo hi \<sigma> rl)
  case 0 then show ?case by simp
next
  case (Suc f)
  note r = Suc.prems
  let ?n0 = "n0I gridL lo hi"
  let ?nd = "node_impl p q N gridL ?n0 lo hi rl (hbL p q N rl)"
  have ag: "agree N (Rf rl) (Hbf (hbL p q N rl)) (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>)" by (rule agree_state [OF r])
  have trm: "terminalI p band ?nd = terminal p q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band"
    by (simp only: terminalI_eq [OF g] terminal_agree [OF ag])
  have cnd: "candsI p band ?nd = cands p q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band"
    by (simp only: candsI_eq [OF g] cands_agree [OF ag])
  have ok: "all_okI p gridL lo hi ?n0 = all_ok p lo hi ?n0" by (rule all_okI_eq [OF g])
  have IHs: "verify_impl p q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) (stepL p N IN kl rl s) (hbL p q N (stepL p N IN kl rl s))
             = verify p q N IN (n0I gridL) band Dmax wmin f lo hi (s # \<sigma>)"
    if "s < M" for s
    by (rule Suc.IH [OF rows_inv_step [OF k r that]])
  have la: "list_all (\<lambda>s. let rl' = stepL p N IN kl rl s in verify_impl p q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) rl' (hbL p q N rl'))
                     (cands p q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band)
          = list_all (\<lambda>s. verify p q N IN (n0I gridL) band Dmax wmin f lo hi (s # \<sigma>))
                     (cands p q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band)"
    unfolding list_all_iff Let_def by (intro ball_cong refl) (simp add: IHs cands_lt)
  show ?case
    unfolding verify_impl.simps verify.simps Let_def trm cnd ok
    using Suc.IH [OF r] la [unfolded Let_def] by simp
qed

text \<open>The top-level entry point.\<close>
definition check_sector :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "check_sector p q N IN band Dmax wmin f lo hi =
     (let kl = kernelL p q N; gl = gridLst p in
      verify_impl p q N IN kl gl band Dmax wmin f lo hi [] kl (hbL p q N kl))"

theorem check_sector_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
    and chk: "check_sector p q N IN band Dmax wmin f lo hi"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "stops_within (fpos q) N bd tm ts t Dmax"
proof -
  have "verify p q N IN (n0I (gridLst p)) band Dmax wmin f lo hi []"
    using chk unfolding check_sector_def Let_def
    by (simp only: verify_impl_eq [OF kernel_inv_kernelL gridLst_nth rows_inv_init])
  then show ?thesis by (rule verify_sound [OF IN bd tr _ _ t]) simp_all
qed

end
