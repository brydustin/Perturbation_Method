theory Symmetry
  imports Search
begin

section \<open>Excitations that agree on the array\<close>

text \<open>Only the entries \<open>j < N\<close> of an excitation matter.\<close>
definition ceq :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> bool" where
  "ceq N cc cc' \<longleftrightarrow> (\<forall>j < N. cc j = cc' j)"

lemma ceq_refl: "ceq N cc cc" by (simp add: ceq_def)
lemma ceq_sym: "ceq N cc cc' \<Longrightarrow> ceq N cc' cc" by (simp add: ceq_def)
lemma ceq_trans: "ceq N cc cc' \<Longrightarrow> ceq N cc' cc'' \<Longrightarrow> ceq N cc cc''" by (simp add: ceq_def)

lemma patt_ceq: "ceq N cc cc' \<Longrightarrow> patt p N cc \<phi> = patt p N cc' \<phi>"
  by (simp add: patt_def ceq_def)

lemma sq_ceq: "ceq N cc cc' \<Longrightarrow> sq p N cc m = sq p N cc' m"
  by (simp add: sq_def patt_ceq)

lemma is_peak_ceq: "ceq N cc cc' \<Longrightarrow> is_peak p N cc m = is_peak p N cc' m"
  by (simp add: is_peak_def sq_ceq)

lemma peaks_ceq: "ceq N cc cc' \<Longrightarrow> peaks p N cc = peaks p N cc'"
  by (simp add: peaks_def is_peak_ceq)

lemma mains_ceq: "ceq N cc cc' \<Longrightarrow> mains p N cc t = mains p N cc' t"
  by (simp add: mains_def peaks_ceq)

lemma sqmax_ceq: "ceq N cc cc' \<Longrightarrow> sqmax p N cc = sqmax p N cc'"
  by (simp add: sqmax_def sq_ceq [of N cc cc' p])

lemma eligible_ceq: "ceq N cc cc' \<Longrightarrow> eligible p N bd cc t m0 = eligible p N bd cc' t m0"
  by (simp add: eligible_def peaks_ceq sqmax_ceq sq_ceq [of N cc cc' p])

lemma elig_ceq: "ceq N cc cc' \<Longrightarrow> elig p N bd tm cc t = elig p N bd tm cc' t"
  by (simp add: elig_def mains_ceq eligible_ceq)

lemma sel_ceq: "ceq N cc cc' \<Longrightarrow> sel p N cc E = sel p N cc' E"
  by (simp add: sel_def sq_ceq [of N cc cc' p])

lemma corr_ceq: "ceq N cc cc' \<Longrightarrow> ceq N (corr p N s cc) (corr p N s cc')"
  by (simp add: corr_def ceq_def patt_ceq [of N cc cc'])

section \<open>Transport of runs along a symmetry (Lemma 2.7)\<close>

definition transport :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where
  "transport \<pi> cc j = cc (\<pi> j)"

text \<open>A symmetry: a permutation \<open>\<pi>\<close> of the element indices, a bijection \<open>g\<close> of the grid indices and a
  map \<open>G\<close> of angles with
  (H1) \<open>steer p (G \<phi>) j = steer p \<phi> (\<pi> j)\<close> for \<open>j < N\<close>;
  (H2) \<open>steer p (grid (g m)) j = steer p (G (grid m)) j\<close> for \<open>m < M\<close>;
  (H3) neighbours go to neighbours; (H4) \<open>G\<close> is an isometry on the grid.\<close>

context
  fixes p :: "nat \<Rightarrow> real \<times> real" and N :: nat and \<pi> :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat" and G :: "real \<Rightarrow> real"
  assumes pi_bij: "bij_betw \<pi> {..<N} {..<N}"
    and g_bij: "bij_betw g {..<M} {..<M}"
    and H1: "\<And>\<phi> j. j < N \<Longrightarrow> steer p (G \<phi>) j = steer p \<phi> (\<pi> j)"
    and H2: "\<And>m j. m < M \<Longrightarrow> steer p (grid (g m)) j = steer p (G (grid m)) j"
    and H3: "\<And>m. m < M \<Longrightarrow> {g (prev_idx m), g (next_idx m)} = {prev_idx (g m), next_idx (g m)}"
    and H4: "\<And>m t. m < M \<Longrightarrow> cdist (grid (g m)) (G t) = cdist (grid m) t"
begin

lemma patt_transport: "patt p N (transport \<pi> cc) (G \<phi>) = patt p N cc \<phi>"
proof -
  have "patt p N (transport \<pi> cc) (G \<phi>) = (\<Sum>j<N. steer p \<phi> (\<pi> j) * cc (\<pi> j))"
    by (simp add: patt_def transport_def H1)
  also have "\<dots> = (\<Sum>j<N. steer p \<phi> j * cc j)"
    using pi_bij by (rule sum.reindex_bij_betw [of \<pi> "{..<N}" "{..<N}" "\<lambda>j. steer p \<phi> j * cc j"])
  finally show ?thesis by (simp add: patt_def)
qed

lemma g_lt: "m < M \<Longrightarrow> g m < M"
  using g_bij by (auto simp: bij_betw_def)

lemma g_inj: "m < M \<Longrightarrow> m' < M \<Longrightarrow> g m = g m' \<Longrightarrow> m = m'"
  using g_bij by (auto simp: bij_betw_def inj_on_def)

lemma patt_grid_transport: "m < M \<Longrightarrow> patt p N (transport \<pi> cc) (grid (g m)) = patt p N cc (grid m)"
proof -
  assume "m < M"
  have "patt p N (transport \<pi> cc) (grid (g m)) = patt p N (transport \<pi> cc) (G (grid m))"
    by (simp add: patt_def H2 [OF \<open>m < M\<close>])
  then show ?thesis by (simp add: patt_transport)
qed

lemma sq_transport: "m < M \<Longrightarrow> sq p N (transport \<pi> cc) (g m) = sq p N cc m"
  by (simp add: sq_def patt_grid_transport)

lemma peak_transport: "m < M \<Longrightarrow> is_peak p N (transport \<pi> cc) (g m) = is_peak p N cc m"
proof -
  assume m: "m < M"
  have pl: "prev_idx m < M" and nl: "next_idx m < M" by (simp_all add: prev_idx_def next_idx_def M_def)
  have nb: "{sq p N (transport \<pi> cc) (prev_idx (g m)), sq p N (transport \<pi> cc) (next_idx (g m))}
          = {sq p N cc (prev_idx m), sq p N cc (next_idx m)}"
  proof -
    have "{sq p N (transport \<pi> cc) (prev_idx (g m)), sq p N (transport \<pi> cc) (next_idx (g m))}
          = sq p N (transport \<pi> cc) ` {prev_idx (g m), next_idx (g m)}" by simp
    also have "\<dots> = sq p N (transport \<pi> cc) ` {g (prev_idx m), g (next_idx m)}" by (simp add: H3 [OF m])
    also have "\<dots> = {sq p N cc (prev_idx m), sq p N cc (next_idx m)}" by (simp add: sq_transport pl nl)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding is_peak_def sq_transport [OF m] using nb by (auto simp: doubleton_eq_iff)
qed

lemma peaks_transport: "peaks p N (transport \<pi> cc) = g ` peaks p N cc"
proof -
  have "peaks p N (transport \<pi> cc) = {m'. m' < M \<and> is_peak p N (transport \<pi> cc) m'}" by (simp add: peaks_def)
  also have "\<dots> = {g m | m. m < M \<and> is_peak p N (transport \<pi> cc) (g m)}"
  proof (intro set_eqI iffI)
    fix m' assume "m' \<in> {m'. m' < M \<and> is_peak p N (transport \<pi> cc) m'}"
    then obtain m where "m < M" "g m = m'" using g_bij by (auto simp: bij_betw_def) (metis imageE lessThan_iff)
    then show "m' \<in> {g m | m. m < M \<and> is_peak p N (transport \<pi> cc) (g m)}"
      using \<open>m' \<in> {m'. m' < M \<and> is_peak p N (transport \<pi> cc) m'}\<close> by auto
  qed (auto simp: g_lt)
  also have "\<dots> = {g m | m. m < M \<and> is_peak p N cc m}" by (rule Collect_cong) (auto simp: peak_transport)
  finally show ?thesis by (auto simp: peaks_def)
qed

lemma mains_transport: "mains p N (transport \<pi> cc) (G t) = g ` mains p N cc t"
proof -
  have "mains p N (transport \<pi> cc) (G t) = {m' \<in> g ` peaks p N cc. \<forall>q' \<in> g ` peaks p N cc. cdist (grid m') (G t) \<le> cdist (grid q') (G t)}"
    by (simp add: mains_def peaks_transport)
  also have "\<dots> = g ` {m \<in> peaks p N cc. \<forall>q \<in> peaks p N cc. cdist (grid m) t \<le> cdist (grid q) t}"
    by (auto simp: H4 peaks_def)
  finally show ?thesis by (simp add: mains_def)
qed

lemma sqmax_transport: "sqmax p N (transport \<pi> cc) = sqmax p N cc"
proof -
  have "sq p N (transport \<pi> cc) ` {..<M} = sq p N (transport \<pi> cc) ` g ` {..<M}"
    using g_bij by (simp add: bij_betw_def)
  also have "\<dots> = sq p N cc ` {..<M}" by (auto simp: image_image sq_transport)
  finally show ?thesis by (simp add: sqmax_def)
qed

lemma inband_transport: "m < M \<Longrightarrow> in_band bd (G t) (g m) = in_band bd t m"
  by (simp add: in_band_def H4 split: option.split)

lemma eligible_transport:
  assumes "m0 < M"
  shows "eligible p N bd (transport \<pi> cc) (G t) (g m0) = g ` eligible p N bd cc t m0"
proof -
  have "eligible p N bd (transport \<pi> cc) (G t) (g m0)
        = {m' \<in> g ` peaks p N cc. m' \<noteq> g m0 \<and> sqmax p N cc / 100 < sq p N (transport \<pi> cc) m' \<and> in_band bd (G t) m'}"
    by (simp add: eligible_def peaks_transport sqmax_transport)
  also have "\<dots> = g ` {m \<in> peaks p N cc. m \<noteq> m0 \<and> sqmax p N cc / 100 < sq p N cc m \<and> in_band bd t m}"
    using assms by (auto simp: peaks_def sq_transport inband_transport dest: g_inj)
  finally show ?thesis by (simp add: eligible_def)
qed

lemma sel_transport: "E \<subseteq> {..<M} \<Longrightarrow> sel p N (transport \<pi> cc) (g ` E) = g ` sel p N cc E"
  by (auto simp: sel_def sq_transport subset_iff)

lemma corr_transport: "s < M \<Longrightarrow> ceq N (corr p N (g s) (transport \<pi> cc)) (transport \<pi> (corr p N s cc))"
proof -
  assume s: "s < M"
  have st: "steer p (grid (g s)) j = steer p (grid s) (\<pi> j)" if "j < N" for j
    using H2 [OF s] H1 [OF that] by simp
  show ?thesis
    unfolding ceq_def
  proof (intro allI impI)
    fix j assume j: "j < N"
    have "corr p N (g s) (transport \<pi> cc) j
          = transport \<pi> cc j - patt p N (transport \<pi> cc) (grid (g s)) / of_nat N * cnj (steer p (grid (g s)) j)"
      by (simp add: corr_def)
    also have "\<dots> = cc (\<pi> j) - patt p N cc (grid s) / of_nat N * cnj (steer p (grid s) (\<pi> j))"
      by (simp only: transport_def st [OF j] patt_grid_transport [OF s])
    also have "\<dots> = transport \<pi> (corr p N s cc) j" by (simp add: transport_def corr_def)
    finally show "corr p N (g s) (transport \<pi> cc) j = transport \<pi> (corr p N s cc) j" .
  qed
qed

lemma c0_transport: "ceq N (c0 p (G t)) (transport \<pi> (c0 p t))"
  by (simp add: ceq_def c0_def transport_def H1)

text \<open>The pulled-back tie rules: at focus \<open>t\<close> choose what the given rules choose at \<open>G t\<close>, read back through \<open>g\<close>.\<close>
definition pull :: "(nat set \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> nat" where
  "pull f W = (if W \<subseteq> {..<M} \<and> W \<noteq> {} then the_inv_into {..<M} g (f (g ` W)) else (SOME x. x \<in> W))"

lemma pull_in:
  assumes f: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> f W \<in> W" and W: "W \<subseteq> {..<M}" "W \<noteq> {}" "finite W"
  shows "pull f W \<in> W" and "g (pull f W) = f (g ` W)"
proof -
  have inj: "inj_on g {..<M}" using g_bij by (simp add: bij_betw_def)
  have "f (g ` W) \<in> g ` W" using W by (intro f) simp_all
  then obtain x where x: "x \<in> W" "f (g ` W) = g x" by auto
  have xM: "x \<in> {..<M}" using x(1) W(1) by auto
  have inv: "the_inv_into {..<M} g (g x) = x" by (rule the_inv_into_f_f [OF inj xM])
  have pw: "pull f W = x" using W(1,2) x(2) inv by (simp add: pull_def)
  show "pull f W \<in> W" "g (pull f W) = f (g ` W)" using pw x by simp_all
qed

lemma pull_tie_rule:
  assumes "tie_rule tm' ts'"
  shows "tie_rule (pull tm') (pull ts')"
proof -
  have gen: "pull f W \<in> W" if f: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> f W \<in> W" and W: "W \<noteq> {}" "finite W" for f W
  proof (cases "W \<subseteq> {..<M}")
    case True show ?thesis by (rule pull_in [OF f True W])
  next
    case False then show ?thesis using W by (simp add: pull_def some_in_eq)
  qed
  have tm: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> tm' W \<in> W" and ts: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> ts' W \<in> W"
    using assms by (simp_all add: tie_rule_def)
  show ?thesis unfolding tie_rule_def by (auto simp: gen [OF tm] gen [OF ts])
qed

lemma mains_subset: "mains p N cc t \<subseteq> {..<M}"
  by (auto simp: mains_def peaks_def)

lemma elig_subset: "elig p N bd tm cc t \<subseteq> {..<M}"
  by (auto simp: elig_def eligible_def peaks_def)

text \<open>The eligible set at \<open>G t\<close> of a transported excitation is the transported eligible set.\<close>
lemma elig_transport_gen:
  assumes tr: "tie_rule tm' ts'" and ce: "ceq N cc' (transport \<pi> cc)"
  shows "elig p N bd tm' cc' (G t) = g ` elig p N bd (pull tm') cc t"
proof (cases "peaks p N cc = {}")
  case True
  then have "peaks p N cc' = {}" using peaks_ceq [OF ce] peaks_transport by simp
  with True show ?thesis by (simp add: elig_empty_no_peaks)
next
  case False
  have mne: "mains p N cc t \<noteq> {}" by (rule mains_nonempty [OF False])
  have fin: "finite (mains p N cc t)" by (rule finite_mains)
  have tm'_in: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> tm' W \<in> W" using tr by (simp add: tie_rule_def)
  let ?m0 = "pull tm' (mains p N cc t)"
  have m0: "?m0 \<in> mains p N cc t" by (rule pull_in(1) [OF tm'_in mains_subset mne fin])
  have gm0: "g ?m0 = tm' (g ` mains p N cc t)" by (rule pull_in(2) [OF tm'_in mains_subset mne fin])
  have m0M: "?m0 < M" using m0 mains_subset by auto
  have "elig p N bd tm' cc' (G t) = eligible p N bd (transport \<pi> cc) (G t) (tm' (mains p N (transport \<pi> cc) (G t)))"
    by (simp add: elig_def mains_ceq [OF ce] eligible_ceq [OF ce])
  also have "\<dots> = eligible p N bd (transport \<pi> cc) (G t) (g ?m0)" by (simp add: mains_transport gm0)
  also have "\<dots> = g ` eligible p N bd cc t ?m0" by (rule eligible_transport [OF m0M])
  finally show ?thesis by (simp add: elig_def)
qed

text \<open>The run at \<open>G t\<close> under \<open>(tm', ts')\<close> is the transported run at \<open>t\<close> under the pulled-back rules.\<close>
lemma run_transport:
  assumes tr: "tie_rule tm' ts'"
  shows "ceq N (run p N bd tm' ts' (G t) n) (transport \<pi> (run p N bd (pull tm') (pull ts') t n))"
proof (induction n)
  case 0 show ?case by (simp add: c0_transport)
next
  case (Suc n)
  let ?cc' = "run p N bd tm' ts' (G t) n"
  let ?cc = "run p N bd (pull tm') (pull ts') t n"
  let ?E = "elig p N bd (pull tm') ?cc t"
  have E': "elig p N bd tm' ?cc' (G t) = g ` ?E" by (rule elig_transport_gen [OF tr Suc.IH])
  show ?case
  proof (cases "?E = {}")
    case True
    then show ?thesis using Suc.IH E' by simp
  next
    case False
    have ts'_in: "\<And>W. W \<noteq> {} \<Longrightarrow> finite W \<Longrightarrow> ts' W \<in> W" using tr by (simp add: tie_rule_def)
    have sne: "sel p N ?cc ?E \<noteq> {}" by (intro sel_nonempty False finite_elig)
    have ssub: "sel p N ?cc ?E \<subseteq> {..<M}" using sel_subset elig_subset by blast
    have sfin: "finite (sel p N ?cc ?E)" by (rule finite_subset [OF sel_subset finite_elig])
    let ?s = "pull ts' (sel p N ?cc ?E)"
    have s_in: "?s \<in> sel p N ?cc ?E" by (rule pull_in(1) [OF ts'_in ssub sne sfin])
    have gs: "g ?s = ts' (g ` sel p N ?cc ?E)" by (rule pull_in(2) [OF ts'_in ssub sne sfin])
    have sM: "?s < M" using s_in ssub by auto
    have sel': "sel p N ?cc' (elig p N bd tm' ?cc' (G t)) = g ` sel p N ?cc ?E"
      by (simp add: E' sel_ceq [OF Suc.IH] sel_transport [OF elig_subset])
    have ne': "elig p N bd tm' ?cc' (G t) \<noteq> {}" using E' False by simp
    have "run p N bd tm' ts' (G t) (Suc n) = corr p N (ts' (sel p N ?cc' (elig p N bd tm' ?cc' (G t)))) ?cc'"
      by (simp only: run.simps if_not_P [OF ne'])
    also have "ts' (sel p N ?cc' (elig p N bd tm' ?cc' (G t))) = g ?s" by (simp only: sel' gs [symmetric])
    finally have r1: "run p N bd tm' ts' (G t) (Suc n) = corr p N (g ?s) ?cc'" .
    have r2: "run p N bd (pull tm') (pull ts') t (Suc n) = corr p N ?s ?cc"
      by (simp only: run.simps if_not_P [OF False])
    have "ceq N (corr p N (g ?s) ?cc') (transport \<pi> (corr p N ?s ?cc))"
      by (rule ceq_trans [OF corr_ceq [OF Suc.IH] corr_transport [OF sM]])
    then show ?thesis unfolding r1 r2 .
  qed
qed

lemma stops_transport:
  assumes tr: "tie_rule tm' ts'"
  shows "stops_within p N bd tm' ts' (G t) D \<longleftrightarrow> stops_within p N bd (pull tm') (pull ts') t D"
proof -
  have "elig p N bd tm' (run p N bd tm' ts' (G t) n) (G t) = {} \<longleftrightarrow> elig p N bd (pull tm') (run p N bd (pull tm') (pull ts') t n) t = {}" for n
    by (simp add: elig_transport_gen [OF tr run_transport [OF tr]])
  then show ?thesis by (simp add: stops_within_def)
qed

text \<open>If every run at focus \<open>t\<close> stops within \<open>D\<close> corrections, so does every run at focus \<open>G t\<close>.\<close>
theorem all_rules_transport:
  assumes "\<And>tm ts. tie_rule tm ts \<Longrightarrow> stops_within p N bd tm ts t D"
  shows "tie_rule tm' ts' \<Longrightarrow> stops_within p N bd tm' ts' (G t) D"
  using stops_transport assms pull_tie_rule by blast

end

end
