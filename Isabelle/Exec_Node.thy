theory Exec_Node
  imports Search
begin

section \<open>Congruence: the abstract functions only look at indices below the bounds\<close>

lemma map_upt_cong: "(\<And>j. j < n \<Longrightarrow> f j = g j) \<Longrightarrow> map f [0..<n] = map g [0..<n]"
  by (intro map_cong) auto

lemma FF_ivl_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "FF_ivl p q N R X = FF_ivl p q N R' X"
  unfolding FF_ivl_def
  by (intro arg_cong [where f = "csum p"] map_upt_cong arg_cong2 [where f = "cmul p"] refl assms)

lemma FF1_ivl_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "FF1_ivl p q N R X = FF1_ivl p q N R' X"
  unfolding FF1_ivl_def
  by (intro arg_cong [where f = "csum p"] map_upt_cong arg_cong2 [where f = "cmul p"] refl assms)

lemma SS_ivl_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "SS_ivl p q N R X = SS_ivl p q N R' X"
  unfolding SS_ivl_def by (rule arg_cong [where f = "cnorm2 p"]) (rule FF_ivl_cong [OF assms])

lemma SS1_ivl_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "SS1_ivl p q N R X = SS1_ivl p q N R' X"
  unfolding SS1_ivl_def
  by (intro arg_cong2 [where f = "(*)"] arg_cong2 [where f = "inner_ivl p"] refl FF_ivl_cong FF1_ivl_cong assms)

lemma Hc_ivl_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "Hc_ivl p q N R = Hc_ivl p q N R'"
  unfolding Hc_ivl_def Bc_ivl_def Dc_ivl_def Ec_ivl_def
  by (intro arg_cong2 [where f = "(*)"] arg_cong2 [where f = "(+)"] refl
            arg_cong [where f = "fsum p"] map_upt_cong arg_cong [where f = "absr p"] assms)

lemma lo_b_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "lo_b p q N R Hb lo hi = lo_b p q N R' Hb lo hi"
  unfolding lo_b_def rad_def
  by (simp only: SS_ivl_cong [OF assms, where p = p and q = q and X = "interval_of (tc lo hi)"] SS1_ivl_cong [OF assms, where p = p and q = q and X = "interval_of (tc lo hi)"])

lemma up_b_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R' j"
  shows "up_b p q N R Hb lo hi = up_b p q N R' Hb lo hi"
  unfolding up_b_def rad_def
  by (simp only: SS_ivl_cong [OF assms, where p = p and q = q and X = "interval_of (tc lo hi)"] SS1_ivl_cong [OF assms, where p = p and q = q and X = "interval_of (tc lo hi)"])

lemma diff_b_cong:
  assumes "\<And>j. j < N \<Longrightarrow> R j = R2 j" "\<And>j. j < N \<Longrightarrow> R' j = R2' j"
  shows "diff_b p q N R R' Hb Hb' lo hi = diff_b p q N R2 R2' Hb Hb' lo hi"
  unfolding diff_b_def rad2_def
  by (simp only: SS_ivl_cong [OF assms(1), where p = p and q = q and X = "interval_of (tc lo hi)"] SS1_ivl_cong [OF assms(1), where p = p and q = q and X = "interval_of (tc lo hi)"]
                 SS_ivl_cong [OF assms(2), where p = p and q = q and X = "interval_of (tc lo hi)"] SS1_ivl_cong [OF assms(2), where p = p and q = q and X = "interval_of (tc lo hi)"])

text \<open>Agreement of node data on the relevant indices.\<close>
definition agree :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> float) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> float) \<Rightarrow> bool" where
  "agree N R Hb R' Hb' \<longleftrightarrow> (\<forall>m < M. (\<forall>j < N. R m j = R' m j) \<and> Hb m = Hb' m)"

lemma agreeD: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> j < N \<Longrightarrow> R m j = R' m j"
  and agreeH: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> Hb m = Hb' m"
  by (simp_all add: agree_def)

lemma LOB_agree: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> LOB p q N R Hb lo hi m = LOB p q N R' Hb' lo hi m"
  unfolding LOB_def by (simp add: agreeH) (intro lo_b_cong agreeD)

lemma UPB_agree: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> UPB p q N R Hb lo hi m = UPB p q N R' Hb' lo hi m"
  unfolding UPB_def by (simp add: agreeH) (intro up_b_cong agreeD)

lemma DP_agree: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> DP p q N R Hb lo hi m = DP p q N R' Hb' lo hi m"
  unfolding DP_def using prev_lt [of m] by (simp add: agreeH) (intro diff_b_cong agreeD)

lemma DN_agree: "agree N R Hb R' Hb' \<Longrightarrow> m < M \<Longrightarrow> DN p q N R Hb lo hi m = DN p q N R' Hb' lo hi m"
  unfolding DN_def using next_lt [of m] by (simp add: agreeH) (intro diff_b_cong agreeD)

lemma PP_agree: "agree N R Hb R' Hb' \<Longrightarrow> PP p q N R Hb lo hi m = PP p q N R' Hb' lo hi m"
  unfolding PP_def by (auto simp: DP_agree DN_agree)

lemma CP_agree: "agree N R Hb R' Hb' \<Longrightarrow> CP p q N R Hb lo hi m = CP p q N R' Hb' lo hi m"
  unfolding CP_def by (auto simp: DP_agree DN_agree)

lemma PM_agree: "agree N R Hb R' Hb' \<Longrightarrow> PM p q N R Hb lo hi n0 m = PM p q N R' Hb' lo hi n0 m"
  unfolding PM_def by (simp add: PP_agree CP_agree)

lemma run_ok_agree: "agree N R Hb R' Hb' \<Longrightarrow> run_ok p q N R Hb lo hi n0 RS = run_ok p q N R' Hb' lo hi n0 RS"
  unfolding run_ok_def by (simp add: PP_agree)

lemma EXC_agree: "agree N R Hb R' Hb' \<Longrightarrow> EXC p q N R Hb lo hi n0 m = EXC p q N R' Hb' lo hi n0 m"
  unfolding EXC_def by (simp add: run_ok_agree)

lemma GL_agree: "agree N R Hb R' Hb' \<Longrightarrow> GL p q N R Hb lo hi = GL p q N R' Hb' lo hi"
  unfolding GL_def by (intro arg_cong [where f = Max] image_cong refl) (simp add: LOB_agree)

lemma US_agree: "agree N R Hb R' Hb' \<Longrightarrow> US p q N R Hb lo hi n0 band = US p q N R' Hb' lo hi n0 band"
proof -
  assume a: "agree N R Hb R' Hb'"
  have "{m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}
      = {m. PP p q N R' Hb' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R' Hb' lo hi n0 m}"
    by (simp add: PP_agree [OF a] EXC_agree [OF a])
  moreover have "(UPB p q N R Hb lo hi) ` {m. PP p q N R' Hb' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R' Hb' lo hi n0 m}
      = (UPB p q N R' Hb' lo hi) ` {m. PP p q N R' Hb' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R' Hb' lo hi n0 m}"
  proof (intro image_cong refl)
    fix x assume "x \<in> {m. PP p q N R' Hb' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R' Hb' lo hi n0 m}"
    then have "x < M" by (simp only: mem_Collect_eq PP_def)
    then show "UPB p q N R Hb lo hi x = UPB p q N R' Hb' lo hi x" by (rule UPB_agree [OF a])
  qed
  ultimately show ?thesis unfolding US_def by simp
qed

lemma TH_agree: "agree N R Hb R' Hb' \<Longrightarrow> TH p q N R Hb lo hi = TH p q N R' Hb' lo hi"
  unfolding TH_def by (simp add: GL_agree)

lemma terminal_agree: "agree N R Hb R' Hb' \<Longrightarrow> terminal p q N R Hb lo hi n0 band = terminal p q N R' Hb' lo hi n0 band"
  unfolding terminal_def by (simp add: US_agree TH_agree)

lemma LL_agree: "agree N R Hb R' Hb' \<Longrightarrow> LL p q N R Hb lo hi n0 band = LL p q N R' Hb' lo hi n0 band"
proof -
  assume a: "agree N R Hb R' Hb'"
  have "{k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}
      = {k. CP p q N R' Hb' lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R' Hb' lo hi n0 k}"
    by (simp add: CP_agree [OF a] PM_agree [OF a])
  moreover have "(LOB p q N R Hb lo hi) ` {k. CP p q N R' Hb' lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R' Hb' lo hi n0 k}
      = (LOB p q N R' Hb' lo hi) ` {k. CP p q N R' Hb' lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R' Hb' lo hi n0 k}"
  proof (intro image_cong refl)
    fix x assume "x \<in> {k. CP p q N R' Hb' lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R' Hb' lo hi n0 k}"
    then have "x < M" by (simp only: mem_Collect_eq CP_def)
    then show "LOB p q N R Hb lo hi x = LOB p q N R' Hb' lo hi x" by (rule LOB_agree [OF a])
  qed
  ultimately show ?thesis unfolding LL_def by simp
qed

lemma cand_agree:
  assumes a: "agree N R Hb R' Hb'"
  shows "cand p q N R Hb lo hi n0 band m = cand p q N R' Hb' lo hi n0 band m"
proof (cases "m < M")
  case True
  then show ?thesis unfolding cand_def
    by (simp only: PP_agree [OF a] EXC_agree [OF a] TH_agree [OF a] LL_agree [OF a] UPB_agree [OF a True])
next
  case False
  then show ?thesis unfolding cand_def by (simp add: PP_def)
qed

lemma cands_agree: "agree N R Hb R' Hb' \<Longrightarrow> cands p q N R Hb lo hi n0 band = cands p q N R' Hb' lo hi n0 band"
  unfolding cands_def by (intro filter_cong refl) (simp add: cand_agree)

end
