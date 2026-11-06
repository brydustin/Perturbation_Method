theory Search
  imports Classify
begin

section \<open>The candidates and the search procedure (Definition 6.1)\<close>

definition cands :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> float) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> float interval option \<Rightarrow> nat list" where
  "cands p q N R Hb lo hi n0 band = filter (cand p q N R Hb lo hi n0 band) [0..<M]"

definition all_ok :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> bool" where
  "all_ok p lo hi n0 \<longleftrightarrow> (\<forall>m < M. dist_ok p lo hi n0 m)"

text \<open>The reference node data for a correction sequence \<open>\<sigma>\<close>.\<close>
definition Rref :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> civ" where
  "Rref p q N IN \<sigma> = rows_ivl p q N IN \<sigma>"
definition Hbref :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> float" where
  "Hbref p q N IN \<sigma> m = upper (Hc_ivl p q N (rows_ivl p q N IN \<sigma> m))"

lemma node_ok_Rref: "1 / real N \<in>\<^sub>r IN \<Longrightarrow> node_ok q N \<sigma> (Rref p q N IN \<sigma>) (Hbref p q N IN \<sigma>)"
  unfolding Rref_def Hbref_def by (rule node_ok_ref)

text \<open>The search.  \<open>n0f lo hi\<close> supplies the integers of the distance reduction; \<open>Dmax\<close> is the depth cap,
  \<open>wmin\<close> the smallest sector width that is still split, and \<open>f\<close> is fuel that bounds the recursion.\<close>
fun verify :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow>
               float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat list \<Rightarrow> bool" where
  "verify p q N IN n0f band Dmax wmin 0 lo hi \<sigma> = False"
| "verify p q N IN n0f band Dmax wmin (Suc f) lo hi \<sigma> =
     (let R = Rref p q N IN \<sigma>; Hb = Hbref p q N IN \<sigma>; n0 = n0f lo hi in
      if \<not> all_ok p lo hi n0 then False
      else if terminal p q N R Hb lo hi n0 band then True
      else let K = cands p q N R Hb lo hi n0 band in
        if (length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo
          then verify p q N IN n0f band Dmax wmin f lo (tc lo hi) \<sigma> \<and> verify p q N IN n0f band Dmax wmin f (tc lo hi) hi \<sigma>
        else if K = [] then True
        else if Dmax \<le> length \<sigma> then False
        else list_all (\<lambda>s. verify p q N IN n0f band Dmax wmin f lo hi (s # \<sigma>)) K)"

section \<open>Soundness (Proposition 6.2)\<close>

lemma mains_nonempty:
  assumes "peaks p' N cc \<noteq> {}"
  shows "mains p' N cc t \<noteq> {}"
proof -
  have fin: "finite ((\<lambda>m. cdist (grid m) t) ` peaks p' N cc)" by (simp add: finite_peaks)
  from assms obtain m0 where m0: "m0 \<in> peaks p' N cc" by blast
  have ne: "(\<lambda>m. cdist (grid m) t) ` peaks p' N cc \<noteq> {}" using m0 by blast
  have "Min ((\<lambda>m. cdist (grid m) t) ` peaks p' N cc) \<in> (\<lambda>m. cdist (grid m) t) ` peaks p' N cc"
    by (rule Min_in [OF fin ne])
  then obtain m where m: "m \<in> peaks p' N cc" "cdist (grid m) t = Min ((\<lambda>m. cdist (grid m) t) ` peaks p' N cc)" by auto
  have "cdist (grid m) t \<le> cdist (grid k) t" if "k \<in> peaks p' N cc" for k
    using m(2) fin that by (simp add: Min_le)
  with m(1) show ?thesis by (auto simp: mains_def)
qed

lemma finite_mains: "finite (mains p' N cc t)"
  by (rule finite_subset [of _ "peaks p' N cc"]) (auto simp: mains_def finite_peaks)

text \<open>With a tie rule, the chosen main lobe is a nearest peak whenever there is a peak at all.\<close>
lemma tm_mains:
  assumes "tie_rule tm ts" "peaks p' N cc \<noteq> {}"
  shows "tm (mains p' N cc t) \<in> mains p' N cc t"
  using assms mains_nonempty [OF assms(2), of t] finite_mains by (simp add: tie_rule_def)

lemma elig_empty_no_peaks: "peaks p' N cc = {} \<Longrightarrow> elig p' N bd tm cc t = {}"
  by (auto simp: elig_def eligible_def)

text \<open>The run after \<open>n\<close> corrections, and what a non-stop step does to the correction list.\<close>
lemma corrs_step:
  assumes "elig (fpos q) N bd tm (run (fpos q) N bd tm ts t n) t \<noteq> {}"
  shows "corrs (fpos q) N bd tm ts t (Suc n) =
         ts (sel (fpos q) N (run (fpos q) N bd tm ts t n) (elig (fpos q) N bd tm (run (fpos q) N bd tm ts t n) t)) # corrs (fpos q) N bd tm ts t n"
  using assms by simp

lemma length_corrs_le: "length (corrs (fpos q) N bd tm ts t n) \<le> n"
  by (induction n) auto

lemma corrs_full_no_stop:
  assumes "corrs (fpos q) N bd tm ts t n = \<sigma>" "length \<sigma> = n"
  shows "\<And>i. i < n \<Longrightarrow> elig (fpos q) N bd tm (run (fpos q) N bd tm ts t i) t \<noteq> {}"
proof -
  have "length (corrs (fpos q) N bd tm ts t n) < n" if "i < n" "elig (fpos q) N bd tm (run (fpos q) N bd tm ts t i) t = {}" for i
    using that
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    show ?case
    proof (cases "i < n")
      case True
      then have "length (corrs (fpos q) N bd tm ts t n) < n" using Suc by simp
      then show ?thesis by (auto simp: length_corrs_le [THEN le_imp_less_Suc] less_Suc_eq_le)
    next
      case False
      with Suc.prems have "i = n" by simp
      with Suc.prems(2) show ?thesis using length_corrs_le [of q N bd tm ts t n] by simp
    qed
  qed
  with assms show "\<And>i. i < n \<Longrightarrow> elig (fpos q) N bd tm (run (fpos q) N bd tm ts t i) t \<noteq> {}" by fastforce
qed

text \<open>The main soundness theorem: a successful search certifies that every run with focus in the sector,
  whose first corrections are \<open>\<sigma>\<close>, stops within \<open>Dmax\<close> corrections.\<close>
theorem verify_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
  shows "verify p q N IN n0f band Dmax wmin f lo hi \<sigma> \<Longrightarrow> length \<sigma> \<le> Dmax \<Longrightarrow>
         real_of_float lo \<le> t \<Longrightarrow> t \<le> real_of_float hi \<Longrightarrow>
         corrs (fpos q) N bd tm ts t (length \<sigma>) = \<sigma> \<Longrightarrow>
         stops_within (fpos q) N bd tm ts t Dmax"
proof (induction f arbitrary: lo hi \<sigma>)
  case 0 then show ?case by simp
next
  case (Suc f)
  note V = Suc.prems(1) and len = Suc.prems(2) and t = Suc.prems(3,4) and cs = Suc.prems(5)
  define R where "R = Rref p q N IN \<sigma>"
  define Hb where "Hb = Hbref p q N IN \<sigma>"
  define n0 where "n0 = n0f lo hi"
  define K where "K = cands p q N R Hb lo hi n0 band"
  have nok: "node_ok q N \<sigma> R Hb" unfolding R_def Hb_def by (rule node_ok_Rref [OF IN])
  have ok: "all_ok p lo hi n0" using V by (auto simp: n0_def Let_def split: if_splits)
  then have okm: "\<And>m. m < M \<Longrightarrow> dist_ok p lo hi n0 m" by (simp add: all_ok_def)
  let ?c = "run (fpos q) N bd tm ts t (length \<sigma>)"
  have c_exc: "?c = exc (fpos q) N (c0 (fpos q) t) \<sigma>" by (simp add: run_exc cs)
  let ?E = "elig (fpos q) N bd tm ?c t"
  text \<open>If nothing is eligible now, the run stops at \<open>length \<sigma> \<le> Dmax\<close>.\<close>
  have stop_now: "?E = {} \<Longrightarrow> stops_within (fpos q) N bd tm ts t Dmax"
    using len by (auto simp: stops_within_def)
  text \<open>Otherwise the chosen main lobe is a nearest peak, and the next correction is a candidate.\<close>
  have next_cand: "?E \<noteq> {} \<Longrightarrow> ts (sel (fpos q) N ?c ?E) \<in> set K \<and> ts (sel (fpos q) N ?c ?E) < M"
  proof -
    assume ne: "?E \<noteq> {}"
    have pk: "peaks (fpos q) N ?c \<noteq> {}" using ne elig_empty_no_peaks by blast
    have m0: "tm (mains (fpos q) N ?c t) \<in> mains (fpos q) N ?c t" by (rule tm_mains [OF tr pk])
    have "sel (fpos q) N ?c ?E \<noteq> {}" by (intro sel_nonempty ne finite_elig)
    with tr have s: "ts (sel (fpos q) N ?c ?E) \<in> sel (fpos q) N ?c ?E"
      by (simp add: tie_rule_def finite_subset [OF sel_subset finite_elig])
    let ?ce = "exc (fpos q) N (c0 (fpos q) t) \<sigma>"
    have cs: "cand p q N R Hb lo hi n0 band (ts (sel (fpos q) N ?ce (eligible (fpos q) N bd ?ce t (tm (mains (fpos q) N ?ce t)))))"
      using Classify.sel_cand [OF nok okm t bd m0 [unfolded c_exc] s [unfolded elig_def c_exc]] by simp
    have "cand p q N R Hb lo hi n0 band (ts (sel (fpos q) N ?c ?E))"
      using cs unfolding elig_def c_exc .
    then show ?thesis by (simp add: K_def cands_def cand_def PP_def)
  qed
  text \<open>Case analysis on the search.\<close>
  show ?case
  proof (cases "terminal p q N R Hb lo hi n0 band")
    case True
    have "?E = {}"
    proof (cases "peaks (fpos q) N ?c = {}")
      case True then show ?thesis by (rule elig_empty_no_peaks)
    next
      case False
      have m0: "tm (mains (fpos q) N ?c t) \<in> mains (fpos q) N ?c t" by (rule tm_mains [OF tr False])
      let ?ce = "exc (fpos q) N (c0 (fpos q) t) \<sigma>"
      have "eligible (fpos q) N bd ?ce t (tm (mains (fpos q) N ?ce t)) = {}"
        using Classify.terminal_sound [OF nok okm t bd m0 [unfolded c_exc] True] by simp
      then show ?thesis unfolding elig_def c_exc .
    qed
    then show ?thesis by (rule stop_now)
  next
    case nt: False
    show ?thesis
    proof (cases "(length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo")
      case True
      have both: "verify p q N IN n0f band Dmax wmin f lo (tc lo hi) \<sigma>" "verify p q N IN n0f band Dmax wmin f (tc lo hi) hi \<sigma>"
        using V ok nt True by (simp_all add: R_def Hb_def n0_def K_def Let_def)
      show ?thesis
      proof (cases "t \<le> real_of_float (tc lo hi)")
        case True
        show ?thesis by (rule Suc.IH [OF both(1) len t(1) True cs])
      next
        case False
        then have ge: "real_of_float (tc lo hi) \<le> t" by simp
        show ?thesis by (rule Suc.IH [OF both(2) len ge t(2) cs])
      qed
    next
      case nosplit: False
      show ?thesis
      proof (cases "K = []")
        case True
        then have "?E = {}" using next_cand by auto
        then show ?thesis by (rule stop_now)
      next
        case Kne: False
        have cap: "\<not> Dmax \<le> length \<sigma>"
          using V ok nt nosplit Kne unfolding verify.simps Let_def R_def [symmetric] Hb_def [symmetric] n0_def [symmetric] K_def [symmetric]
          by (auto split: if_splits)
        have la: "list_all (\<lambda>s. verify p q N IN n0f band Dmax wmin f lo hi (s # \<sigma>)) K"
          using V ok nt nosplit Kne cap unfolding verify.simps Let_def R_def [symmetric] Hb_def [symmetric] n0_def [symmetric] K_def [symmetric]
          by (auto split: if_splits)
        show ?thesis
        proof (cases "?E = {}")
          case True then show ?thesis by (rule stop_now)
        next
          case False
          let ?s = "ts (sel (fpos q) N ?c ?E)"
          have sK: "?s \<in> set K" using next_cand [OF False] by simp
          have v': "verify p q N IN n0f band Dmax wmin f lo hi (?s # \<sigma>)"
            using la sK by (simp add: list_all_iff)
          have cs': "corrs (fpos q) N bd tm ts t (length (?s # \<sigma>)) = ?s # \<sigma>"
            using corrs_step [OF False] cs by simp
          show ?thesis using Suc.IH [OF v' _ t cs'] cap by simp
        qed
      qed
    qed
  qed
qed

end
