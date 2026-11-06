theory G_Discrete
  imports G_Method
begin

section \<open>Fact 1: every stretch of samples above the threshold contains a peak\<close>

text \<open>Samples above the threshold \<open>th\<close>, and steps between neighbouring ones.\<close>
definition above :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "above p N c th = {j. j < M \<and> sq p N c j > th}"

definition step :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> (nat \<times> nat) set" where
  "step p N c th = {(j, k). j \<in> above p N c th \<and> k \<in> above p N c th \<and> (k = next_idx j \<or> k = prev_idx j)}"

lemma reach_above: "(j, k) \<in> (step p N c th)\<^sup>* \<Longrightarrow> j \<in> above p N c th \<Longrightarrow> k \<in> above p N c th"
  by (induction rule: rtrancl_induct) (auto simp: step_def)

text \<open>A set of indices closed under \<open>next_idx\<close> that contains one index contains all.\<close>
lemma next_closed_all:
  assumes q: "q < M" "q \<in> Z" and cl: "\<And>x. x \<in> Z \<Longrightarrow> next_idx x \<in> Z" and k: "k < M"
  shows "k \<in> Z"
proof -
  have it: "(q + i) mod M \<in> Z" for i
  proof (induction i)
    case 0 then show ?case using q by simp
  next
    case (Suc i)
    have "(q + Suc i) mod M = next_idx ((q + i) mod M)"
      by (simp add: next_idx_def mod_Suc_eq)
    with cl [OF Suc] show ?case by simp
  qed
  have "(q + (k + M - q)) mod M = k" using q k by simp
  with it [of "k + M - q"] show ?thesis by simp
qed

text \<open>Fact 1, in the form used: from any sample above the threshold one can walk, through
  neighbouring samples above the threshold, to a peak, unless all samples are reachable.\<close>
lemma walk_to_peak:
  assumes j: "j \<in> above p N c th"
  shows "(\<exists>q. (j, q) \<in> (step p N c th)\<^sup>* \<and> q \<in> fpeaks p N c) \<or> (\<forall>k < M. (j, k) \<in> (step p N c th)\<^sup>*)"
proof -
  define C where "C = {k. (j, k) \<in> (step p N c th)\<^sup>*}"
  have CA: "C \<subseteq> above p N c th" using j reach_above by (auto simp: C_def)
  have CM: "C \<subseteq> {..<M}" using CA by (auto simp: above_def)
  have finC: "finite C" using CM finite_subset by blast
  have jC: "j \<in> C" by (simp add: C_def)
  have grow: "k' \<in> C" if "k \<in> C" "k' \<in> above p N c th" "k' = next_idx k \<or> k' = prev_idx k" for k k'
  proof -
    have "(k, k') \<in> step p N c th" using that CA by (auto simp: step_def)
    with that(1) show ?thesis by (auto simp: C_def intro: rtrancl_into_rtrancl)
  qed
  define mu where "mu = Max (sq p N c ` C)"
  define Z where "Z = {k \<in> C. sq p N c k = mu}"
  have mu_ge: "sq p N c k \<le> mu" if "k \<in> C" for k
    unfolding mu_def using finC that by (intro Max_ge) auto
  have "mu \<in> sq p N c ` C" unfolding mu_def using finC jC by (intro Max_in) auto
  then obtain z where z: "z \<in> Z" by (auto simp: Z_def)
  show ?thesis
  proof (cases "\<forall>x \<in> Z. next_idx x \<in> Z")
    case True
    have zM: "z < M" using z CM by (auto simp: Z_def)
    have "k \<in> Z" if k: "k < M" for k
      by (rule next_closed_all [OF zM z _ k]) (use True in blast)
    then have "\<forall>k < M. (j, k) \<in> (step p N c th)\<^sup>*" by (auto simp: Z_def C_def)
    then show ?thesis by blast
  next
    case False
    then obtain q where qZ: "q \<in> Z" and nq: "next_idx q \<notin> Z" by blast
    have qC: "q \<in> C" and qmu: "sq p N c q = mu" using qZ by (auto simp: Z_def)
    have qA: "q \<in> above p N c th" using qC CA by auto
    have below: "sq p N c k < mu" if kC: "k \<notin> C" and kq: "k = next_idx q \<or> k = prev_idx q" for k
    proof -
      have "k \<notin> above p N c th"
      proof
        assume "k \<in> above p N c th"
        then have "k \<in> C" by (rule grow [OF qC _ kq])
        with kC show False by contradiction
      qed
      moreover have "k < M" using kq by (auto simp: idx_next_lt idx_prev_lt)
      ultimately have "sq p N c k \<le> th" by (simp add: above_def)
      moreover have "th < sq p N c q" using qA by (simp add: above_def)
      ultimately show ?thesis using qmu by linarith
    qed
    have n_lt: "sq p N c (next_idx q) < sq p N c q"
    proof (cases "next_idx q \<in> C")
      case True
      have "sq p N c (next_idx q) \<le> mu" by (rule mu_ge [OF True])
      moreover have "sq p N c (next_idx q) \<noteq> mu" using nq True by (simp add: Z_def)
      ultimately show ?thesis using qmu by linarith
    next
      case False
      show ?thesis using below [OF False disjI1 [OF refl]] qmu by simp
    qed
    have p_le: "sq p N c (prev_idx q) \<le> sq p N c q"
    proof (cases "prev_idx q \<in> C")
      case True
      show ?thesis using mu_ge [OF True] qmu by simp
    next
      case False
      show ?thesis using below [OF False disjI2 [OF refl]] qmu by simp
    qed
    have qM: "q < M" using qA by (simp add: above_def)
    have "q \<in> fpeaks p N c"
      using qM n_lt p_le by (simp add: fpeaks_def is_fpeak_def)
    with qC show ?thesis by (auto simp: C_def)
  qed
qed

text \<open>At a stop, every sample above the lowered threshold is joined, through neighbouring samples
  above it, to the main peak or to a peak inside the band.\<close>
theorem walk_to_main:
  assumes j: "j \<in> above p N c th"
    and stop: "\<And>q. q \<in> fpeaks p N c \<Longrightarrow> sq p N c q > th \<Longrightarrow>
                 q = m0 \<or> q = prev_idx m0 \<or> q = next_idx m0 \<or> q \<in> X"
    and m0: "fpeaks p N c \<noteq> {} \<Longrightarrow> m0 \<in> fpeaks p N c"
  shows "\<exists>q. (j, q) \<in> (step p N c th)\<^sup>* \<and> (q = m0 mod M \<or> q \<in> X)"
  using walk_to_peak [OF j]
proof
  assume "\<exists>q. (j, q) \<in> (step p N c th)\<^sup>* \<and> q \<in> fpeaks p N c"
  then obtain q where jq: "(j, q) \<in> (step p N c th)\<^sup>*" and qP: "q \<in> fpeaks p N c" by blast
  have qA: "q \<in> above p N c th" by (rule reach_above [OF jq j])
  then have qth: "sq p N c q > th" by (simp add: above_def)
  have m0P: "m0 \<in> fpeaks p N c" using m0 qP by blast
  then have m0M: "m0 < M" by (simp add: fpeaks_def)
  consider "q = m0" | "q = prev_idx m0" | "q = next_idx m0" | "q \<in> X" using stop [OF qP qth] by blast
  then show ?thesis
  proof cases
    case 1 with jq m0M show ?thesis by auto
  next
    case 2
    have nq: "next_idx q = m0" using 2 next_prev [OF m0M] by simp
    have "sq p N c q \<ge> sq p N c (next_idx q)" using qP by (simp add: fpeaks_def is_fpeak_def)
    moreover have "sq p N c m0 \<ge> sq p N c (prev_idx m0)" using m0P by (simp add: fpeaks_def is_fpeak_def)
    ultimately have "sq p N c m0 = sq p N c q" using nq 2 by simp
    then have "m0 \<in> above p N c th" using qth m0M by (simp add: above_def)
    with qA nq have "(q, m0) \<in> step p N c th" by (auto simp: step_def)
    with jq m0M show ?thesis by (auto intro: rtrancl_into_rtrancl)
  next
    case 3
    have pq: "prev_idx q = m0" using 3 prev_next [OF m0M] by simp
    have "sq p N c q \<ge> sq p N c (prev_idx q)" using qP by (simp add: fpeaks_def is_fpeak_def)
    moreover have "sq p N c m0 \<ge> sq p N c (next_idx m0)" using m0P by (simp add: fpeaks_def is_fpeak_def)
    ultimately have "sq p N c m0 = sq p N c q" using pq 3 by simp
    then have "m0 \<in> above p N c th" using qth m0M by (simp add: above_def)
    with qA pq have "(q, m0) \<in> step p N c th" by (auto simp: step_def)
    with jq m0M show ?thesis by (auto intro: rtrancl_into_rtrancl)
  next
    case 4 with jq show ?thesis by blast
  qed
next
  assume all: "\<forall>k < M. (j, k) \<in> (step p N c th)\<^sup>*"
  have "m0 mod M < M" by (simp add: M_def)
  with all show ?thesis by blast
qed

end
