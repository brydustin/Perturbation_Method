theory GC_Classify
  imports "Perturbative_Termination.Classify" "Sidelobe_Guarantee.G_Method"
begin

section \<open>The index sets of the changed method\<close>

text \<open>As in \<open>Classify\<close>, with three changes: a possible peak needs \<open>\<ge>\<close> instead of \<open>>\<close> on both
  sides; the threshold is lowered by the float \<open>dlf\<close>; and a certainly eligible index must not be a
  neighbour of a possible main peak.\<close>

definition PPg where "PPg p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 \<le> upper (DP p q N R Hb lo hi m) \<and> 0 \<le> upper (DN p q N R Hb lo hi m)"
definition PMg where "PMg p q N R Hb lo hi n0 m \<longleftrightarrow> PPg p q N R Hb lo hi m \<and>
   (\<forall>k < M. CP p q N R Hb lo hi k \<longrightarrow> DMIN p lo hi n0 m \<le> DMAX p lo hi n0 k)"

definition run_okg where "run_okg p q N R Hb lo hi n0 RS \<longleftrightarrow>
   (\<forall>r \<in> RS. PPg p q N R Hb lo hi r) \<and>
   (\<forall>r \<in> RS. \<forall>k < M. PPg p q N R Hb lo hi k \<and> k \<notin> RS \<longrightarrow> DMAX p lo hi n0 r < DMIN p lo hi n0 k)"
definition EXCg where "EXCg p q N R Hb lo hi n0 m \<longleftrightarrow> m < M \<and>
   (run_okg p q N R Hb lo hi n0 {m} \<or> run_okg p q N R Hb lo hi n0 {m, next_idx m} \<or> run_okg p q N R Hb lo hi n0 {prev_idx m, m})"

definition USg where "USg p q N R Hb lo hi n0 band =
   Max (insert 0 ((UPB p q N R Hb lo hi) ` {m. PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m}))"

definition THg where "THg p dlf q N R Hb lo hi = lower (TH p q N R Hb lo hi) - dlf"

definition gterminal where "gterminal p dlf q N R Hb lo hi n0 band \<longleftrightarrow> USg p q N R Hb lo hi n0 band \<le> THg p dlf q N R Hb lo hi"

definition LLg where "LLg p q N R Hb lo hi n0 band =
   Max (insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and>
     \<not> PMg p q N R Hb lo hi n0 k \<and> \<not> PMg p q N R Hb lo hi n0 (prev_idx k) \<and> \<not> PMg p q N R Hb lo hi n0 (next_idx k)}))"

definition gcand where "gcand p dlf q N R Hb lo hi n0 band m \<longleftrightarrow>
   PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m \<and>
   THg p dlf q N R Hb lo hi \<le> UPB p q N R Hb lo hi m \<and>
   \<not> (0 < LLg p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi m < LLg p q N R Hb lo hi n0 band)"

lemma PPg_lt: "PPg p q N R Hb lo hi m \<Longrightarrow> m < M" by (simp add: PPg_def)

section \<open>Soundness\<close>

context
  fixes p :: nat and q :: "nat \<Rightarrow> float \<times> float" and N :: nat and R :: "nat \<Rightarrow> nat \<Rightarrow> civ" and Hb :: "nat \<Rightarrow> float"
    and \<sigma> :: "nat list" and lo hi :: float and n0 :: "nat \<Rightarrow> int" and band :: "float interval option"
    and bd :: "real option" and t :: real and dlf :: float
  assumes nok: "node_ok q N \<sigma> R Hb"
    and ok: "\<And>m. m < M \<Longrightarrow> dist_ok p lo hi n0 m"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
    and bd: "band_in bd band"
begin

abbreviation (input) "gcx \<equiv> exc (fpos q) N (c0 (fpos q) t) \<sigma>"
abbreviation (input) "gSx \<equiv> SQ q N \<sigma> t"
abbreviation (input) "gdlx \<equiv> real_of_float dlf"

lemma gS_lo: "m < M \<Longrightarrow> real_of_float (LOB p q N R Hb lo hi m) \<le> gSx m"
  by (rule Classify.S_lo [OF nok ok t bd])
lemma gS_up: "m < M \<Longrightarrow> gSx m \<le> real_of_float (UPB p q N R Hb lo hi m)"
  by (rule Classify.S_up [OF nok ok t bd])
lemma gDPl: "m < M \<Longrightarrow> gSx m - gSx (prev_idx m) \<in>\<^sub>r DP p q N R Hb lo hi m"
  by (rule Classify.DPl [OF nok ok t bd])
lemma gDNl: "m < M \<Longrightarrow> gSx m - gSx (next_idx m) \<in>\<^sub>r DN p q N R Hb lo hi m"
  by (rule Classify.DNl [OF nok ok t bd])
lemma gd_lo: "m < M \<Longrightarrow> real_of_float (DMIN p lo hi n0 m) \<le> cdist (grid m) t"
  by (rule Classify.d_lo [OF nok ok t bd])
lemma gd_up: "m < M \<Longrightarrow> cdist (grid m) t \<le> real_of_float (DMAX p lo hi n0 m)"
  by (rule Classify.d_up [OF nok ok t bd])
lemma g_inband_PO: "m < M \<Longrightarrow> in_band bd t m \<Longrightarrow> PO p lo hi n0 band m"
  by (rule Classify.inband_PO [OF nok ok t bd])
lemma g_CO_inband: "m < M \<Longrightarrow> CO p lo hi n0 band m \<Longrightarrow> in_band bd t m"
  by (rule Classify.CO_inband [OF nok ok t bd])
lemma g_TH_le: "real_of_float (lower (TH p q N R Hb lo hi)) \<le> sqmax (fpos q) N gcx / 100"
  by (rule Classify.TH_le [OF nok ok t bd])

lemma fpeak_PPg: "m \<in> fpeaks (fpos q) N gcx \<Longrightarrow> PPg p q N R Hb lo hi m"
proof -
  assume "m \<in> fpeaks (fpos q) N gcx"
  then have m: "m < M" and d1: "0 \<le> gSx m - gSx (prev_idx m)" and d2: "0 \<le> gSx m - gSx (next_idx m)"
    by (auto simp: fpeaks_def is_fpeak_def)
  from in_real_upper [OF gDPl [OF m]] d1 have "0 \<le> real_of_float (upper (DP p q N R Hb lo hi m))" by linarith
  moreover from in_real_upper [OF gDNl [OF m]] d2 have "0 \<le> real_of_float (upper (DN p q N R Hb lo hi m))" by linarith
  ultimately show ?thesis using m by (simp add: PPg_def)
qed

lemma CP_fpeak: "CP p q N R Hb lo hi m \<Longrightarrow> m \<in> fpeaks (fpos q) N gcx"
proof -
  assume cp: "CP p q N R Hb lo hi m"
  then have m: "m < M" and l1: "0 < real_of_float (lower (DP p q N R Hb lo hi m))"
    and l2: "0 < real_of_float (lower (DN p q N R Hb lo hi m))" by (simp_all add: CP_def)
  from in_real_lower [OF gDPl [OF m]] l1 have "0 < gSx m - gSx (prev_idx m)" by linarith
  moreover from in_real_lower [OF gDNl [OF m]] l2 have "0 < gSx m - gSx (next_idx m)" by linarith
  ultimately show ?thesis using m by (simp add: fpeaks_def is_fpeak_def)
qed

lemma main_PMg: "m0 \<in> fmains (fpos q) N gcx t \<Longrightarrow> PMg p q N R Hb lo hi n0 m0"
proof -
  assume m0: "m0 \<in> fmains (fpos q) N gcx t"
  then have pk: "m0 \<in> fpeaks (fpos q) N gcx" by (simp add: fmains_def)
  have "DMIN p lo hi n0 m0 \<le> DMAX p lo hi n0 k" if "k < M" "CP p q N R Hb lo hi k" for k
  proof -
    have "k \<in> fpeaks (fpos q) N gcx" by (rule CP_fpeak [OF that(2)])
    with m0 have "cdist (grid m0) t \<le> cdist (grid k) t" by (simp add: fmains_def)
    with gd_lo [of m0] gd_up [of k] pk that(1) show ?thesis by (simp add: fpeaks_def; linarith)
  qed
  with fpeak_PPg [OF pk] show ?thesis by (simp add: PMg_def)
qed

text \<open>Nothing in an excluded run is eligible: the run contains the main peak, and the method
  excludes the main peak's neighbours.\<close>
lemma EXg_not_elig:
  assumes ex: "EXCg p q N R Hb lo hi n0 m" and m0: "m0 \<in> fmains (fpos q) N gcx t"
  shows "m \<notin> geligible (fpos q) N gdlx bd gcx t m0"
proof
  assume el: "m \<in> geligible (fpos q) N gdlx bd gcx t m0"
  then have pk: "m \<in> fpeaks (fpos q) N gcx" and ne: "m \<noteq> m0" "m \<noteq> prev_idx m0" "m \<noteq> next_idx m0"
    by (simp_all add: geligible_def)
  have mM: "m < M" using pk by (simp add: fpeaks_def)
  have m0pk: "m0 \<in> fpeaks (fpos q) N gcx" and near: "cdist (grid m0) t \<le> cdist (grid m) t"
    using m0 pk by (auto simp: fmains_def)
  have m0M: "m0 < M" using m0pk by (simp add: fpeaks_def)
  from ex obtain RS where RS: "run_okg p q N R Hb lo hi n0 RS" "m \<in> RS"
    and R2: "RS = {m} \<or> RS = {m, next_idx m} \<or> RS = {prev_idx m, m}" by (auto simp: EXCg_def)
  have "m0 \<in> RS"
  proof (rule ccontr)
    assume nin: "m0 \<notin> RS"
    have "PPg p q N R Hb lo hi m0" by (rule fpeak_PPg [OF m0pk])
    with RS nin m0M have "DMAX p lo hi n0 m < DMIN p lo hi n0 m0" by (auto simp: run_okg_def)
    with gd_up [OF mM] gd_lo [OF m0M] have "cdist (grid m) t < cdist (grid m0) t" by (simp add: less_float.rep_eq)
    with near show False by simp
  qed
  with R2 have "m0 = m \<or> m0 = next_idx m \<or> m0 = prev_idx m" by auto
  moreover have "m0 = next_idx m \<Longrightarrow> m = prev_idx m0" using prev_next [OF mM] by simp
  moreover have "m0 = prev_idx m \<Longrightarrow> m = next_idx m0" using next_prev [OF mM] by simp
  ultimately show False using ne by auto
qed

lemma THg_le: "real_of_float (THg p dlf q N R Hb lo hi) \<le> sqmax (fpos q) N gcx / 100 - gdlx"
  using g_TH_le by (simp add: THg_def)

lemma gelig_props:
  assumes m0: "m0 \<in> fmains (fpos q) N gcx t" and el: "m \<in> geligible (fpos q) N gdlx bd gcx t m0"
  shows "PPg p q N R Hb lo hi m" "PO p lo hi n0 band m" "\<not> EXCg p q N R Hb lo hi n0 m"
proof -
  have pk: "m \<in> fpeaks (fpos q) N gcx" and ib: "in_band bd t m" using el by (simp_all add: geligible_def)
  show "PPg p q N R Hb lo hi m" by (rule fpeak_PPg [OF pk])
  show "PO p lo hi n0 band m" using pk ib by (intro g_inband_PO) (simp add: fpeaks_def)
  show "\<not> EXCg p q N R Hb lo hi n0 m" using EXg_not_elig [OF _ m0] el by blast
qed

lemma finite_USg_set: "finite (insert 0 ((UPB p q N R Hb lo hi) ` {m. PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m}))"
proof -
  have "{m. PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m} \<subseteq> {..<M}"
    by (auto simp: PPg_def)
  then show ?thesis by (simp add: finite_subset)
qed

lemma gterminal_sound:
  assumes m0: "m0 \<in> fmains (fpos q) N gcx t" and trm: "gterminal p dlf q N R Hb lo hi n0 band"
  shows "geligible (fpos q) N gdlx bd gcx t m0 = {}"
proof (rule ccontr)
  assume "geligible (fpos q) N gdlx bd gcx t m0 \<noteq> {}"
  then obtain m where el: "m \<in> geligible (fpos q) N gdlx bd gcx t m0" by auto
  have props: "PPg p q N R Hb lo hi m" "PO p lo hi n0 band m" "\<not> EXCg p q N R Hb lo hi n0 m"
    by (rule gelig_props [OF m0 el])+
  have "gSx m \<le> real_of_float (UPB p q N R Hb lo hi m)" by (rule gS_up [OF PPg_lt [OF props(1)]])
  also have "UPB p q N R Hb lo hi m \<le> USg p q N R Hb lo hi n0 band"
  proof -
    have "UPB p q N R Hb lo hi m \<in> insert 0 ((UPB p q N R Hb lo hi) ` {m. PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m})"
      by (intro insertI2 imageI CollectI conjI props)
    then show ?thesis unfolding USg_def by (rule Max_ge [OF finite_USg_set])
  qed
  also have "USg p q N R Hb lo hi n0 band \<le> THg p dlf q N R Hb lo hi" using trm by (simp add: gterminal_def)
  finally have "gSx m \<le> real_of_float (THg p dlf q N R Hb lo hi)" by simp
  also have "\<dots> \<le> sqmax (fpos q) N gcx / 100 - gdlx" by (rule THg_le)
  finally have "gSx m \<le> sqmax (fpos q) N gcx / 100 - gdlx" .
  moreover have "sqmax (fpos q) N gcx / 100 - gdlx < gSx m" using el by (simp add: geligible_def)
  ultimately show False by simp
qed

lemma gsel_cand:
  assumes m0: "m0 \<in> fmains (fpos q) N gcx t" and s: "s \<in> sel (fpos q) N gcx (geligible (fpos q) N gdlx bd gcx t m0)"
  shows "gcand p dlf q N R Hb lo hi n0 band s"
proof -
  have el: "s \<in> geligible (fpos q) N gdlx bd gcx t m0" using s by (simp add: sel_def)
  have props: "PPg p q N R Hb lo hi s" "PO p lo hi n0 band s" "\<not> EXCg p q N R Hb lo hi n0 s"
    by (rule gelig_props [OF m0 el])+
  have sM: "s < M" by (rule PPg_lt [OF props(1)])
  have thr: "THg p dlf q N R Hb lo hi \<le> UPB p q N R Hb lo hi s"
  proof -
    have "real_of_float (THg p dlf q N R Hb lo hi) \<le> sqmax (fpos q) N gcx / 100 - gdlx" by (rule THg_le)
    also have "\<dots> < gSx s" using el by (simp add: geligible_def)
    also have "gSx s \<le> real_of_float (UPB p q N R Hb lo hi s)" by (rule gS_up [OF sM])
    finally show ?thesis by simp
  qed
  have m0pk: "m0 \<in> fpeaks (fpos q) N gcx" using m0 by (simp add: fmains_def)
  have m0M: "m0 < M" using m0pk by (simp add: fpeaks_def)
  have pm0: "PMg p q N R Hb lo hi n0 m0" by (rule main_PMg [OF m0])
  have notL: "\<not> (0 < LLg p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi s < LLg p q N R Hb lo hi n0 band)"
  proof
    assume a: "0 < LLg p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi s < LLg p q N R Hb lo hi n0 band"
    define KS where "KS = {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PMg p q N R Hb lo hi n0 k
       \<and> \<not> PMg p q N R Hb lo hi n0 (prev_idx k) \<and> \<not> PMg p q N R Hb lo hi n0 (next_idx k)}"
    have sub: "KS \<subseteq> {..<M}" by (auto simp: KS_def CP_def)
    have fin: "finite (insert 0 ((LOB p q N R Hb lo hi) ` KS))" by (simp add: finite_subset [OF sub])
    have "LLg p q N R Hb lo hi n0 band \<in> insert 0 ((LOB p q N R Hb lo hi) ` KS)"
      unfolding LLg_def KS_def [symmetric] by (intro Max_in fin) simp
    then have "LLg p q N R Hb lo hi n0 band \<in> (LOB p q N R Hb lo hi) ` KS"
      using a unfolding insert_iff by (elim disjE) simp_all
    then obtain k where kk: "k \<in> KS" and Lk: "LLg p q N R Hb lo hi n0 band = LOB p q N R Hb lo hi k" by (rule imageE)
    have k: "CP p q N R Hb lo hi k" "CO p lo hi n0 band k" "\<not> PMg p q N R Hb lo hi n0 k"
      "\<not> PMg p q N R Hb lo hi n0 (prev_idx k)" "\<not> PMg p q N R Hb lo hi n0 (next_idx k)"
      using kk by (simp_all add: KS_def)
    have kM: "k < M" using k(1) by (simp add: CP_def)
    have kpk: "k \<in> fpeaks (fpos q) N gcx" by (rule CP_fpeak [OF k(1)])
    have kib: "in_band bd t k" by (rule g_CO_inband [OF kM k(2)])
    have kne: "k \<noteq> m0" using k(3) pm0 by auto
    have kp: "k \<noteq> prev_idx m0"
    proof
      assume "k = prev_idx m0"
      then have "next_idx k = m0" using next_prev [OF m0M] by simp
      with k(5) pm0 show False by simp
    qed
    have kn: "k \<noteq> next_idx m0"
    proof
      assume "k = next_idx m0"
      then have "prev_idx k = m0" using prev_next [OF m0M] by simp
      with k(4) pm0 show False by simp
    qed
    have "real_of_float (LOB p q N R Hb lo hi k) \<le> gSx k" by (rule gS_lo [OF kM])
    moreover have "gSx s \<le> real_of_float (UPB p q N R Hb lo hi s)" by (rule gS_up [OF sM])
    moreover have "real_of_float (UPB p q N R Hb lo hi s) < real_of_float (LOB p q N R Hb lo hi k)"
      using a Lk by (simp add: less_float.rep_eq)
    ultimately have Sk: "gSx s < gSx k" by linarith
    have "sqmax (fpos q) N gcx / 100 - gdlx < gSx s" using el by (simp add: geligible_def)
    with Sk have "k \<in> geligible (fpos q) N gdlx bd gcx t m0" using kpk kib kne kp kn by (simp add: geligible_def)
    then have "gSx k \<le> gSx s" using s by (simp only: sel_def mem_Collect_eq)
    with Sk show False by simp
  qed
  show ?thesis using props thr notL by (simp add: gcand_def)
qed

end

end
