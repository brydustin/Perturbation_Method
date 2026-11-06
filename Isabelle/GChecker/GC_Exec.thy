theory GC_Exec
  imports GC_Search "Perturbative_Termination.Exec_Search"
begin

section \<open>Congruence of the new index sets in the node data\<close>

lemma PPg_agree: "agree N RR HH RR' HH' \<Longrightarrow> PPg p q N RR HH lo hi m = PPg p q N RR' HH' lo hi m"
  unfolding PPg_def by (auto simp: DP_agree DN_agree)

lemma PMg_agree: "agree N RR HH RR' HH' \<Longrightarrow> PMg p q N RR HH lo hi n0 m = PMg p q N RR' HH' lo hi n0 m"
  unfolding PMg_def by (simp add: PPg_agree CP_agree)

lemma run_okg_agree: "agree N RR HH RR' HH' \<Longrightarrow> run_okg p q N RR HH lo hi n0 RS = run_okg p q N RR' HH' lo hi n0 RS"
  unfolding run_okg_def by (simp add: PPg_agree)

lemma EXCg_agree: "agree N RR HH RR' HH' \<Longrightarrow> EXCg p q N RR HH lo hi n0 m = EXCg p q N RR' HH' lo hi n0 m"
  unfolding EXCg_def by (simp add: run_okg_agree)

lemma USg_agree: "agree N RR HH RR' HH' \<Longrightarrow> USg p q N RR HH lo hi n0 band = USg p q N RR' HH' lo hi n0 band"
proof -
  assume a: "agree N RR HH RR' HH'"
  have "{m. PPg p q N RR HH lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N RR HH lo hi n0 m}
      = {m. PPg p q N RR' HH' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N RR' HH' lo hi n0 m}"
    by (simp add: PPg_agree [OF a] EXCg_agree [OF a])
  moreover have "(UPB p q N RR HH lo hi) ` {m. PPg p q N RR' HH' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N RR' HH' lo hi n0 m}
      = (UPB p q N RR' HH' lo hi) ` {m. PPg p q N RR' HH' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N RR' HH' lo hi n0 m}"
  proof (intro image_cong refl)
    fix x assume "x \<in> {m. PPg p q N RR' HH' lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N RR' HH' lo hi n0 m}"
    then have "x < M" by (simp only: mem_Collect_eq PPg_def)
    then show "UPB p q N RR HH lo hi x = UPB p q N RR' HH' lo hi x" by (rule UPB_agree [OF a])
  qed
  ultimately show ?thesis unfolding USg_def by simp
qed

lemma THg_agree: "agree N RR HH RR' HH' \<Longrightarrow> THg p dlf q N RR HH lo hi = THg p dlf q N RR' HH' lo hi"
  unfolding THg_def by (simp add: TH_agree)

lemma gterminal_agree: "agree N RR HH RR' HH' \<Longrightarrow> gterminal p dlf q N RR HH lo hi n0 band = gterminal p dlf q N RR' HH' lo hi n0 band"
  unfolding gterminal_def by (simp add: USg_agree THg_agree)

lemma LLg_agree: "agree N RR HH RR' HH' \<Longrightarrow> LLg p q N RR HH lo hi n0 band = LLg p q N RR' HH' lo hi n0 band"
proof -
  assume a: "agree N RR HH RR' HH'"
  let ?K = "\<lambda>RR HH. {k. CP p q N RR HH lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PMg p q N RR HH lo hi n0 k
              \<and> \<not> PMg p q N RR HH lo hi n0 (prev_idx k) \<and> \<not> PMg p q N RR HH lo hi n0 (next_idx k)}"
  have "?K RR HH = ?K RR' HH'" by (simp add: CP_agree [OF a] PMg_agree [OF a])
  moreover have "(LOB p q N RR HH lo hi) ` ?K RR' HH' = (LOB p q N RR' HH' lo hi) ` ?K RR' HH'"
  proof (intro image_cong refl)
    fix x assume "x \<in> ?K RR' HH'"
    then have "x < M" by (simp only: mem_Collect_eq CP_def)
    then show "LOB p q N RR HH lo hi x = LOB p q N RR' HH' lo hi x" by (rule LOB_agree [OF a])
  qed
  ultimately show ?thesis unfolding LLg_def by simp
qed

lemma gcand_agree:
  assumes a: "agree N RR HH RR' HH'"
  shows "gcand p dlf q N RR HH lo hi n0 band m = gcand p dlf q N RR' HH' lo hi n0 band m"
proof (cases "m < M")
  case True
  then show ?thesis unfolding gcand_def
    by (simp only: PPg_agree [OF a] EXCg_agree [OF a] THg_agree [OF a] LLg_agree [OF a] UPB_agree [OF a True])
next
  case False
  then show ?thesis unfolding gcand_def by (simp add: PPg_def)
qed

lemma gcands_agree: "agree N RR HH RR' HH' \<Longrightarrow> gcands p dlf q N RR HH lo hi n0 band = gcands p dlf q N RR' HH' lo hi n0 band"
  unfolding gcands_def by (intro filter_cong refl) (simp add: gcand_agree)

section \<open>The new index sets on lists\<close>

definition ppgI :: "node \<Rightarrow> nat \<Rightarrow> bool" where "ppgI nod m \<longleftrightarrow> m < M \<and> 0 \<le> upper (ndp nod ! m) \<and> 0 \<le> upper (ndn nod ! m)"
definition pmgI :: "node \<Rightarrow> nat \<Rightarrow> bool" where
  "pmgI nod m \<longleftrightarrow> ppgI nod m \<and> list_all (\<lambda>k. cpI nod k \<longrightarrow> ndmin nod ! m \<le> ndmax nod ! k) [0..<M]"
definition run_okgI :: "node \<Rightarrow> nat list \<Rightarrow> bool" where
  "run_okgI nod RS \<longleftrightarrow> list_all (ppgI nod) RS \<and>
     list_all (\<lambda>r. list_all (\<lambda>k. ppgI nod k \<and> k \<notin> set RS \<longrightarrow> ndmax nod ! r < ndmin nod ! k) [0..<M]) RS"
definition excgI :: "node \<Rightarrow> nat \<Rightarrow> bool" where
  "excgI nod m \<longleftrightarrow> m < M \<and> (run_okgI nod [m] \<or> run_okgI nod [m, next_idx m] \<or> run_okgI nod [prev_idx m, m])"
definition usgI :: "float interval option \<Rightarrow> node \<Rightarrow> float" where
  "usgI band nod = Max (set (0 # map (\<lambda>m. nupb nod ! m) (filter (\<lambda>m. ppgI nod m \<and> poI band nod m \<and> \<not> excgI nod m) [0..<M])))"
definition thgI :: "nat \<Rightarrow> float \<Rightarrow> node \<Rightarrow> float" where
  "thgI p dlf nod = lower (thI p nod) - dlf"
definition gterminalI :: "nat \<Rightarrow> float \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> bool" where
  "gterminalI p dlf band nod \<longleftrightarrow> usgI band nod \<le> thgI p dlf nod"
definition llgI :: "float interval option \<Rightarrow> node \<Rightarrow> float" where
  "llgI band nod = Max (set (0 # map (\<lambda>k. nlob nod ! k)
     (filter (\<lambda>k. cpI nod k \<and> coI band nod k \<and> \<not> pmgI nod k \<and> \<not> pmgI nod (prev_idx k) \<and> \<not> pmgI nod (next_idx k)) [0..<M])))"
definition gcandI :: "nat \<Rightarrow> float \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> bool" where
  "gcandI p dlf band nod m \<longleftrightarrow> ppgI nod m \<and> poI band nod m \<and> \<not> excgI nod m \<and>
     thgI p dlf nod \<le> nupb nod ! m \<and> \<not> (0 < llgI band nod \<and> nupb nod ! m < llgI band nod)"
definition gcandsI :: "nat \<Rightarrow> float \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> nat list" where
  "gcandsI p dlf band nod = filter (gcandI p dlf band nod) [0..<M]"

context
  fixes p :: nat and q :: "nat \<Rightarrow> float \<times> float" and N :: nat and gridL :: "float interval list"
    and n0 :: "nat \<Rightarrow> int" and lo hi :: float and rl :: "civ list list" and hl :: "float list"
  assumes g: "\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m"
begin

abbreviation (input) "gnd \<equiv> node_impl p q N gridL n0 lo hi rl hl"

lemma ppgI_eq: "ppgI gnd m = PPg p q N (Rf rl) (Hbf hl) lo hi m"
  unfolding ppgI_def PPg_def by (cases "m < M") (simp_all add: node_nth [OF g])

lemma pmgI_eq: "pmgI gnd m = PMg p q N (Rf rl) (Hbf hl) lo hi n0 m"
proof (cases "m < M")
  case True
  have cp: "\<And>k. cpI gnd k = CP p q N (Rf rl) (Hbf hl) lo hi k" by (rule cpI_eq [OF g])
  have "list_all (\<lambda>k. cpI gnd k \<longrightarrow> ndmin gnd ! m \<le> ndmax gnd ! k) [0..<M]
        \<longleftrightarrow> (\<forall>k < M. CP p q N (Rf rl) (Hbf hl) lo hi k \<longrightarrow> DMIN p lo hi n0 m \<le> DMAX p lo hi n0 k)"
    unfolding list_all_iff set_upt cp using True by (auto simp: node_nth [OF g])
  then show ?thesis unfolding pmgI_def PMg_def ppgI_eq by simp
next
  case False
  then show ?thesis unfolding pmgI_def PMg_def ppgI_eq by (simp add: PPg_def)
qed

lemma run_okgI_eq: "list_all (\<lambda>r. r < M) RS \<Longrightarrow> run_okgI gnd RS = run_okg p q N (Rf rl) (Hbf hl) lo hi n0 (set RS)"
  unfolding run_okgI_def run_okg_def list_all_iff set_upt ppgI_eq
  by (auto simp: node_nth [OF g] PPg_def)

lemma excgI_eq: "excgI gnd m = EXCg p q N (Rf rl) (Hbf hl) lo hi n0 m"
  unfolding excgI_def EXCg_def
  by (cases "m < M") (simp_all add: run_okgI_eq next_lt prev_lt)

lemma usgI_eq: "usgI band gnd = USg p q N (Rf rl) (Hbf hl) lo hi n0 band"
proof -
  have "set (map (\<lambda>m. nupb gnd ! m) (filter (\<lambda>m. ppgI gnd m \<and> poI band gnd m \<and> \<not> excgI gnd m) [0..<M]))
        = (UPB p q N (Rf rl) (Hbf hl) lo hi) ` {m. PPg p q N (Rf rl) (Hbf hl) lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N (Rf rl) (Hbf hl) lo hi n0 m}"
  proof -
    have eq1: "{m. PPg p q N (Rf rl) (Hbf hl) lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N (Rf rl) (Hbf hl) lo hi n0 m}
          = set (filter (\<lambda>m. ppgI gnd m \<and> poI band gnd m \<and> \<not> excgI gnd m) [0..<M])"
      by (auto simp: ppgI_eq poI_eq [OF g] excgI_eq PPg_def)
    have eq2: "(\<lambda>m. nupb gnd ! m) x = UPB p q N (Rf rl) (Hbf hl) lo hi x"
      if "x \<in> set (filter (\<lambda>m. ppgI gnd m \<and> poI band gnd m \<and> \<not> excgI gnd m) [0..<M])" for x
      using that by (simp add: node_nth [OF g])
    show ?thesis unfolding set_map eq1 by (rule image_cong [OF refl eq2])
  qed
  then show ?thesis by (simp add: usgI_def USg_def)
qed

lemma thgI_eq: "thgI p dlf gnd = THg p dlf q N (Rf rl) (Hbf hl) lo hi"
  by (simp add: thgI_def THg_def thI_eq [OF g])

lemma gterminalI_eq: "gterminalI p dlf band gnd = gterminal p dlf q N (Rf rl) (Hbf hl) lo hi n0 band"
  by (simp add: gterminalI_def gterminal_def usgI_eq thgI_eq)

lemma llgI_eq: "llgI band gnd = LLg p q N (Rf rl) (Hbf hl) lo hi n0 band"
proof -
  let ?K = "{k. CP p q N (Rf rl) (Hbf hl) lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PMg p q N (Rf rl) (Hbf hl) lo hi n0 k
       \<and> \<not> PMg p q N (Rf rl) (Hbf hl) lo hi n0 (prev_idx k) \<and> \<not> PMg p q N (Rf rl) (Hbf hl) lo hi n0 (next_idx k)}"
  let ?F = "filter (\<lambda>k. cpI gnd k \<and> coI band gnd k \<and> \<not> pmgI gnd k \<and> \<not> pmgI gnd (prev_idx k) \<and> \<not> pmgI gnd (next_idx k)) [0..<M]"
  have "set (map (\<lambda>k. nlob gnd ! k) ?F) = (LOB p q N (Rf rl) (Hbf hl) lo hi) ` ?K"
  proof -
    have eq1: "?K = set ?F"
      by (auto simp: cpI_eq [OF g] coI_eq [OF g] pmgI_eq CP_def)
    have eq2: "(\<lambda>k. nlob gnd ! k) x = LOB p q N (Rf rl) (Hbf hl) lo hi x" if "x \<in> set ?F" for x
      using that by (simp add: node_nth [OF g])
    show ?thesis unfolding set_map eq1 by (rule image_cong [OF refl eq2])
  qed
  then show ?thesis by (simp add: llgI_def LLg_def)
qed

lemma gcandI_eq: "gcandI p dlf band gnd m = gcand p dlf q N (Rf rl) (Hbf hl) lo hi n0 band m"
proof (cases "m < M")
  case True
  then show ?thesis unfolding gcandI_def gcand_def
    by (simp add: ppgI_eq poI_eq [OF g] excgI_eq thgI_eq llgI_eq node_nth [OF g])
next
  case False
  then show ?thesis unfolding gcandI_def gcand_def by (simp add: ppgI_def PPg_def)
qed

lemma gcandsI_eq: "gcandsI p dlf band gnd = gcands p dlf q N (Rf rl) (Hbf hl) lo hi n0 band"
  unfolding gcandsI_def gcands_def by (intro filter_cong refl gcandI_eq)

end

section \<open>The executable search\<close>

fun gverify_impl :: "nat \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list list \<Rightarrow> float interval list \<Rightarrow>
                    float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat list \<Rightarrow> civ list list \<Rightarrow> float list \<Rightarrow> bool" where
  "gverify_impl p dlf q N IN kl gridL band Dmax wmin 0 lo hi \<sigma> rl hl = False"
| "gverify_impl p dlf q N IN kl gridL band Dmax wmin (Suc f) lo hi \<sigma> rl hl =
     (let n0 = n0I gridL lo hi in
      if \<not> all_okI p gridL lo hi n0 then False
      else let nod = node_impl p q N gridL n0 lo hi rl hl in
        if gterminalI p dlf band nod then True
        else let K = gcandsI p dlf band nod in
          if (length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo
            then gverify_impl p dlf q N IN kl gridL band Dmax wmin f lo (tc lo hi) \<sigma> rl hl
               \<and> gverify_impl p dlf q N IN kl gridL band Dmax wmin f (tc lo hi) hi \<sigma> rl hl
          else if K = [] then True
          else if Dmax \<le> length \<sigma> then False
          else list_all (\<lambda>s. let rl' = stepL p N IN kl rl s in
                               gverify_impl p dlf q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) rl' (hbL p q N rl')) K)"

lemma gcands_lt: "s \<in> set (gcands p dlf q N RR HH lo hi n0 band) \<Longrightarrow> s < M"
  by (simp add: gcands_def)

theorem gverify_impl_eq:
  assumes k: "kernel_inv p q N kl" and g: "\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m"
  shows "rows_inv p q N IN \<sigma> rl \<Longrightarrow>
         gverify_impl p dlf q N IN kl gridL band Dmax wmin f lo hi \<sigma> rl (hbL p q N rl)
         = gverify p dlf q N IN (n0I gridL) band Dmax wmin f lo hi \<sigma>"
proof (induction f arbitrary: lo hi \<sigma> rl)
  case 0 then show ?case by simp
next
  case (Suc f)
  note r = Suc.prems
  let ?n0 = "n0I gridL lo hi"
  let ?nod = "node_impl p q N gridL ?n0 lo hi rl (hbL p q N rl)"
  have ag: "agree N (Rf rl) (Hbf (hbL p q N rl)) (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>)" by (rule agree_state [OF r])
  have trm: "gterminalI p dlf band ?nod = gterminal p dlf q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band"
    by (simp only: gterminalI_eq [OF g] gterminal_agree [OF ag])
  have cnd: "gcandsI p dlf band ?nod = gcands p dlf q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band"
    by (simp only: gcandsI_eq [OF g] gcands_agree [OF ag])
  have ok: "all_okI p gridL lo hi ?n0 = all_ok p lo hi ?n0" by (rule all_okI_eq [OF g])
  have IHs: "gverify_impl p dlf q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) (stepL p N IN kl rl s) (hbL p q N (stepL p N IN kl rl s))
             = gverify p dlf q N IN (n0I gridL) band Dmax wmin f lo hi (s # \<sigma>)"
    if "s < M" for s
    by (rule Suc.IH [OF rows_inv_step [OF k r that]])
  have la: "list_all (\<lambda>s. let rl' = stepL p N IN kl rl s in gverify_impl p dlf q N IN kl gridL band Dmax wmin f lo hi (s # \<sigma>) rl' (hbL p q N rl'))
                     (gcands p dlf q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band)
          = list_all (\<lambda>s. gverify p dlf q N IN (n0I gridL) band Dmax wmin f lo hi (s # \<sigma>))
                     (gcands p dlf q N (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>) lo hi ?n0 band)"
    unfolding list_all_iff Let_def by (intro ball_cong refl) (simp add: IHs gcands_lt)
  show ?case
    unfolding gverify_impl.simps gverify.simps Let_def trm cnd ok
    using Suc.IH [OF r] la [unfolded Let_def] by simp
qed

text \<open>The top-level entry point for the changed method.\<close>
definition gcheck_sector :: "nat \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "gcheck_sector p dlf q N IN band Dmax wmin f lo hi =
     (let kl = kernelL p q N; gl = gridLst p in
      gverify_impl p dlf q N IN kl gl band Dmax wmin f lo hi [] kl (hbL p q N kl))"

theorem gcheck_sector_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
    and chk: "gcheck_sector p dlf q N IN band Dmax wmin f lo hi"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "gstops_within (fpos q) N (real_of_float dlf) bd tm ts t Dmax"
proof -
  have "gverify p dlf q N IN (n0I (gridLst p)) band Dmax wmin f lo hi []"
    using chk unfolding gcheck_sector_def Let_def
    by (simp only: gverify_impl_eq [OF kernel_inv_kernelL gridLst_nth rows_inv_init])
  then show ?thesis by (rule gverify_sound [OF IN bd tr _ _ t]) simp_all
qed

end
