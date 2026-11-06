theory GC_Symmetry
  imports "Perturbative_Termination.Symmetry" GC_Search
begin

section \<open>Transport of runs of the changed method along a symmetry\<close>

text \<open>The same hypotheses as in \<open>Symmetry\<close>.  The changed peak rule is symmetric in the two
  neighbours, and the excluded set \<open>{m\<^sub>0, prev m\<^sub>0, next m\<^sub>0}\<close> is mapped onto itself by (H3).\<close>

context
  fixes p :: "nat \<Rightarrow> real \<times> real" and N :: nat and \<pi> :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat" and G :: "real \<Rightarrow> real"
  assumes pi_bij: "bij_betw \<pi> {..<N} {..<N}"
    and g_bij: "bij_betw g {..<M} {..<M}"
    and H1: "\<And>\<phi> j. j < N \<Longrightarrow> steer p (G \<phi>) j = steer p \<phi> (\<pi> j)"
    and H2: "\<And>m j. m < M \<Longrightarrow> steer p (grid (g m)) j = steer p (G (grid m)) j"
    and H3: "\<And>m. m < M \<Longrightarrow> {g (prev_idx m), g (next_idx m)} = {prev_idx (g m), next_idx (g m)}"
    and H4: "\<And>m t. m < M \<Longrightarrow> cdist (grid (g m)) (G t) = cdist (grid m) t"
begin

lemmas symh = pi_bij g_bij H1 H2 H3 H4

lemma gsq_tr: "m < M \<Longrightarrow> sq p N (transport \<pi> cc) (g m) = sq p N cc m"
  by (rule Symmetry.sq_transport [OF symh])

lemma gg_lt: "m < M \<Longrightarrow> g m < M"
  by (rule Symmetry.g_lt [OF symh])

lemma gg_inj: "m < M \<Longrightarrow> m' < M \<Longrightarrow> g m = g m' \<Longrightarrow> m = m'"
  by (rule Symmetry.g_inj [OF symh])

lemma fpeak_transport: "m < M \<Longrightarrow> is_fpeak p N (transport \<pi> cc) (g m) = is_fpeak p N cc m"
proof -
  assume m: "m < M"
  have pl: "prev_idx m < M" and nl: "next_idx m < M" by (simp_all add: prev_idx_def next_idx_def M_def)
  have nb: "{sq p N (transport \<pi> cc) (prev_idx (g m)), sq p N (transport \<pi> cc) (next_idx (g m))}
          = {sq p N cc (prev_idx m), sq p N cc (next_idx m)}"
  proof -
    have "{sq p N (transport \<pi> cc) (prev_idx (g m)), sq p N (transport \<pi> cc) (next_idx (g m))}
          = sq p N (transport \<pi> cc) ` {prev_idx (g m), next_idx (g m)}" by simp
    also have "\<dots> = sq p N (transport \<pi> cc) ` {g (prev_idx m), g (next_idx m)}" by (simp add: H3 [OF m])
    also have "\<dots> = {sq p N cc (prev_idx m), sq p N cc (next_idx m)}" by (simp add: gsq_tr pl nl)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding is_fpeak_def gsq_tr [OF m] using nb by (auto simp: doubleton_eq_iff)
qed

lemma fpeaks_transport: "fpeaks p N (transport \<pi> cc) = g ` fpeaks p N cc"
proof -
  have "fpeaks p N (transport \<pi> cc) = {m'. m' < M \<and> is_fpeak p N (transport \<pi> cc) m'}" by (simp add: fpeaks_def)
  also have "\<dots> = {g m | m. m < M \<and> is_fpeak p N (transport \<pi> cc) (g m)}"
  proof (intro set_eqI iffI)
    fix m' assume a: "m' \<in> {m'. m' < M \<and> is_fpeak p N (transport \<pi> cc) m'}"
    then obtain m where "m < M" "g m = m'" using g_bij by (auto simp: bij_betw_def) (metis imageE lessThan_iff)
    then show "m' \<in> {g m | m. m < M \<and> is_fpeak p N (transport \<pi> cc) (g m)}" using a by auto
  qed (auto simp: gg_lt)
  also have "\<dots> = {g m | m. m < M \<and> is_fpeak p N cc m}" by (rule Collect_cong) (auto simp: fpeak_transport)
  finally show ?thesis by (auto simp: fpeaks_def)
qed

lemma fmains_transport: "fmains p N (transport \<pi> cc) (G t) = g ` fmains p N cc t"
proof -
  have "fmains p N (transport \<pi> cc) (G t) = {m' \<in> g ` fpeaks p N cc. \<forall>q' \<in> g ` fpeaks p N cc. cdist (grid m') (G t) \<le> cdist (grid q') (G t)}"
    by (simp add: fmains_def fpeaks_transport)
  also have "\<dots> = g ` {m \<in> fpeaks p N cc. \<forall>q \<in> fpeaks p N cc. cdist (grid m) t \<le> cdist (grid q) t}"
    by (auto simp: H4 fpeaks_def)
  finally show ?thesis by (simp add: fmains_def)
qed

lemma geligible_transport:
  assumes m0: "m0 < M"
  shows "geligible p N dl bd (transport \<pi> cc) (G t) (g m0) = g ` geligible p N dl bd cc t m0"
proof -
  have pl: "prev_idx m0 < M" and nl: "next_idx m0 < M" by (simp_all add: prev_idx_def next_idx_def M_def)
  have ex: "{g m0, prev_idx (g m0), next_idx (g m0)} = g ` {m0, prev_idx m0, next_idx m0}"
    using H3 [OF m0] by auto
  have "geligible p N dl bd (transport \<pi> cc) (G t) (g m0)
        = {m' \<in> g ` fpeaks p N cc. m' \<notin> {g m0, prev_idx (g m0), next_idx (g m0)}
             \<and> sqmax p N cc / 100 - dl < sq p N (transport \<pi> cc) m' \<and> in_band bd (G t) m'}"
    by (auto simp: geligible_def fpeaks_transport Symmetry.sqmax_transport [OF symh])
  also have "\<dots> = {m' \<in> g ` fpeaks p N cc. m' \<notin> g ` {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N (transport \<pi> cc) m' \<and> in_band bd (G t) m'}"
    by (simp only: ex)
  also have "\<dots> = g ` {m \<in> fpeaks p N cc. m \<notin> {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N cc m \<and> in_band bd t m}"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> {m' \<in> g ` fpeaks p N cc. m' \<notin> g ` {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N (transport \<pi> cc) m' \<and> in_band bd (G t) m'}"
    then obtain m where m: "m \<in> fpeaks p N cc" "x = g m" "g m \<notin> g ` {m0, prev_idx m0, next_idx m0}"
      "sqmax p N cc / 100 - dl < sq p N (transport \<pi> cc) (g m)" "in_band bd (G t) (g m)" by auto
    have mM: "m < M" using m(1) by (simp add: fpeaks_def)
    have "m \<notin> {m0, prev_idx m0, next_idx m0}" using m(3) by auto
    moreover have "sqmax p N cc / 100 - dl < sq p N cc m" using m(4) by (simp add: gsq_tr [OF mM])
    moreover have "in_band bd t m" using m(5) by (simp add: Symmetry.inband_transport [OF symh mM])
    ultimately show "x \<in> g ` {m \<in> fpeaks p N cc. m \<notin> {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N cc m \<and> in_band bd t m}" using m(1,2) by auto
  next
    fix x assume "x \<in> g ` {m \<in> fpeaks p N cc. m \<notin> {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N cc m \<and> in_band bd t m}"
    then obtain m where m: "m \<in> fpeaks p N cc" "x = g m" "m \<notin> {m0, prev_idx m0, next_idx m0}"
      "sqmax p N cc / 100 - dl < sq p N cc m" "in_band bd t m" by auto
    have mM: "m < M" using m(1) by (simp add: fpeaks_def)
    have "g m \<notin> g ` {m0, prev_idx m0, next_idx m0}"
    proof
      assume "g m \<in> g ` {m0, prev_idx m0, next_idx m0}"
      then obtain k where k: "k \<in> {m0, prev_idx m0, next_idx m0}" "g m = g k" by auto
      have "k < M" using k(1) m0 pl nl by auto
      with k mM have "m = k" using gg_inj by blast
      with k(1) m(3) show False by simp
    qed
    then show "x \<in> {m' \<in> g ` fpeaks p N cc. m' \<notin> g ` {m0, prev_idx m0, next_idx m0}
             \<and> sqmax p N cc / 100 - dl < sq p N (transport \<pi> cc) m' \<and> in_band bd (G t) m'}"
      using m mM by (auto simp: gsq_tr Symmetry.inband_transport [OF symh])
  qed
  also have "\<dots> = g ` geligible p N dl bd cc t m0" by (simp add: geligible_def)
  finally show ?thesis .
qed

lemma fmains_subset: "fmains p N cc t \<subseteq> {..<M}"
  by (auto simp: fmains_def fpeaks_def)

lemma gelig_subset: "gelig p N dl bd tm cc t \<subseteq> {..<M}"
  by (auto simp: gelig_def geligible_def fpeaks_def)

lemma finite_fmains: "finite (fmains p N cc t)"
  by (rule finite_subset [OF _ finite_fpeaks]) (auto simp: fmains_def)

lemma gelig_transport_gen:
  assumes tr: "tie_rule tm' ts'" and ce: "ceq N cc' (transport \<pi> cc)"
  shows "gelig p N dl bd tm' cc' (G t) = g ` gelig p N dl bd (pull g tm') cc t"
proof (cases "fpeaks p N cc = {}")
  case True
  have "fpeaks p N cc' = fpeaks p N (transport \<pi> cc)"
    by (simp add: fpeaks_def is_fpeak_def sq_ceq [OF ce])
  then have "fpeaks p N cc' = {}" using True fpeaks_transport by simp
  with True show ?thesis by (simp add: gelig_empty_no_peaks)
next
  case False
  have mne: "fmains p N cc t \<noteq> {}" by (rule fmains_nonempty [OF False])
  have tm'_in: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> tm' W \<in> W" using tr by (simp add: tie_rule_def)
  let ?m0 = "pull g tm' (fmains p N cc t)"
  have m0: "?m0 \<in> fmains p N cc t" by (rule Symmetry.pull_in(1) [OF symh tm'_in fmains_subset mne finite_fmains])
  have gm0: "g ?m0 = tm' (g ` fmains p N cc t)" by (rule Symmetry.pull_in(2) [OF symh tm'_in fmains_subset mne finite_fmains])
  have m0M: "?m0 < M" using m0 fmains_subset by auto
  have fc: "fpeaks p N cc' = fpeaks p N (transport \<pi> cc)" by (simp add: fpeaks_def is_fpeak_def sq_ceq [OF ce])
  have mc: "fmains p N cc' (G t) = fmains p N (transport \<pi> cc) (G t)" by (simp add: fmains_def fc)
  have ec: "geligible p N dl bd cc' (G t) m = geligible p N dl bd (transport \<pi> cc) (G t) m" for m
    by (simp add: geligible_def fc sq_ceq [OF ce] sqmax_ceq [OF ce])
  have "gelig p N dl bd tm' cc' (G t) = geligible p N dl bd (transport \<pi> cc) (G t) (tm' (fmains p N (transport \<pi> cc) (G t)))"
    by (simp add: gelig_def mc ec)
  also have "\<dots> = geligible p N dl bd (transport \<pi> cc) (G t) (g ?m0)" by (simp add: fmains_transport gm0)
  also have "\<dots> = g ` geligible p N dl bd cc t ?m0" by (rule geligible_transport [OF m0M])
  finally show ?thesis by (simp add: gelig_def)
qed

lemma grun_transport:
  assumes tr: "tie_rule tm' ts'"
  shows "ceq N (grun p N dl bd tm' ts' (G t) n) (transport \<pi> (grun p N dl bd (pull g tm') (pull g ts') t n))"
proof (induction n)
  case 0 show ?case by (simp add: Symmetry.c0_transport [OF symh])
next
  case (Suc n)
  let ?cc' = "grun p N dl bd tm' ts' (G t) n"
  let ?cc = "grun p N dl bd (pull g tm') (pull g ts') t n"
  let ?E = "gelig p N dl bd (pull g tm') ?cc t"
  have E': "gelig p N dl bd tm' ?cc' (G t) = g ` ?E" by (rule gelig_transport_gen [OF tr Suc.IH])
  show ?case
  proof (cases "?E = {}")
    case True
    then show ?thesis using Suc.IH E' by simp
  next
    case False
    have ts'_in: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> ts' W \<in> W" using tr by (simp add: tie_rule_def)
    have sne: "sel p N ?cc ?E \<noteq> {}" by (intro sel_nonempty False finite_gelig)
    have ssub: "sel p N ?cc ?E \<subseteq> {..<M}" using sel_subset gelig_subset by blast
    have sfin: "finite (sel p N ?cc ?E)" by (rule finite_subset [OF sel_subset finite_gelig])
    let ?s = "pull g ts' (sel p N ?cc ?E)"
    have s_in: "?s \<in> sel p N ?cc ?E" by (rule Symmetry.pull_in(1) [OF symh ts'_in ssub sne sfin])
    have gs: "g ?s = ts' (g ` sel p N ?cc ?E)" by (rule Symmetry.pull_in(2) [OF symh ts'_in ssub sne sfin])
    have sM: "?s < M" using s_in ssub by auto
    have sel': "sel p N ?cc' (gelig p N dl bd tm' ?cc' (G t)) = g ` sel p N ?cc ?E"
      by (simp add: E' sel_ceq [OF Suc.IH] Symmetry.sel_transport [OF symh gelig_subset])
    have ne': "gelig p N dl bd tm' ?cc' (G t) \<noteq> {}" using E' False by simp
    have "grun p N dl bd tm' ts' (G t) (Suc n) = corr p N (ts' (sel p N ?cc' (gelig p N dl bd tm' ?cc' (G t)))) ?cc'"
      by (simp only: grun.simps if_not_P [OF ne'])
    also have "ts' (sel p N ?cc' (gelig p N dl bd tm' ?cc' (G t))) = g ?s" by (simp only: sel' gs [symmetric])
    finally have r1: "grun p N dl bd tm' ts' (G t) (Suc n) = corr p N (g ?s) ?cc'" .
    have r2: "grun p N dl bd (pull g tm') (pull g ts') t (Suc n) = corr p N ?s ?cc"
      by (simp only: grun.simps if_not_P [OF False])
    have "ceq N (corr p N (g ?s) ?cc') (transport \<pi> (corr p N ?s ?cc))"
      by (rule ceq_trans [OF corr_ceq [OF Suc.IH] Symmetry.corr_transport [OF symh sM]])
    then show ?thesis unfolding r1 r2 .
  qed
qed

lemma gstops_transport:
  assumes tr: "tie_rule tm' ts'"
  shows "gstops_within p N dl bd tm' ts' (G t) D \<longleftrightarrow> gstops_within p N dl bd (pull g tm') (pull g ts') t D"
proof -
  have "gelig p N dl bd tm' (grun p N dl bd tm' ts' (G t) n) (G t) = {} \<longleftrightarrow>
        gelig p N dl bd (pull g tm') (grun p N dl bd (pull g tm') (pull g ts') t n) t = {}" for n
    by (simp add: gelig_transport_gen [OF tr grun_transport [OF tr]])
  then show ?thesis by (simp add: gstops_within_def)
qed

theorem gall_rules_transport:
  assumes "\<And>tm ts. tie_rule tm ts \<Longrightarrow> gstops_within p N dl bd tm ts t D"
  shows "tie_rule tm' ts' \<Longrightarrow> gstops_within p N dl bd tm' ts' (G t) D"
  using gstops_transport assms Symmetry.pull_tie_rule [OF symh] by blast

end

end
