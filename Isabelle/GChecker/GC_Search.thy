theory GC_Search
  imports GC_Classify "Perturbative_Termination.Search"
begin

section \<open>Runs of the changed method as correction lists\<close>

primrec gcorrs :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat list" where
  "gcorrs p N dlv band tm ts t 0 = []"
| "gcorrs p N dlv band tm ts t (Suc n) =
     (if gelig p N dlv band tm (grun p N dlv band tm ts t n) t = {} then gcorrs p N dlv band tm ts t n
      else ts (sel p N (grun p N dlv band tm ts t n) (gelig p N dlv band tm (grun p N dlv band tm ts t n) t))
           # gcorrs p N dlv band tm ts t n)"

lemma grun_exc: "grun p N dlv band tm ts t n = exc p N (c0 p t) (gcorrs p N dlv band tm ts t n)"
  by (induction n) simp_all

lemma finite_gelig: "finite (gelig p N dlv band tm cc t)"
  by (rule finite_subset [OF _ finite_fpeaks]) (auto simp: gelig_def geligible_def)

lemma gelig_empty_no_peaks: "fpeaks p' N cc = {} \<Longrightarrow> gelig p' N dlv bd tm cc t = {}"
  by (auto simp: gelig_def geligible_def)

lemma tm_fmains:
  assumes "tie_rule tm ts" "fpeaks p' N cc \<noteq> {}"
  shows "tm (fmains p' N cc t) \<in> fmains p' N cc t"
proof -
  have "finite (fmains p' N cc t)"
    by (rule finite_subset [OF _ finite_fpeaks]) (auto simp: fmains_def)
  then show ?thesis using assms fmains_nonempty [OF assms(2)] by (auto simp: tie_rule_def)
qed

section \<open>The search for the changed method\<close>

definition gcands :: "nat \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> float)
    \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> float interval option \<Rightarrow> nat list" where
  "gcands p dlf q N R Hb lo hi n0 band = filter (gcand p dlf q N R Hb lo hi n0 band) [0..<M]"

fun gverify :: "nat \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow>
               float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat list \<Rightarrow> bool" where
  "gverify p dlf q N IN n0f band Dmax wmin 0 lo hi \<sigma> = False"
| "gverify p dlf q N IN n0f band Dmax wmin (Suc f) lo hi \<sigma> =
     (let R = Rref p q N IN \<sigma>; Hb = Hbref p q N IN \<sigma>; n0 = n0f lo hi in
      if \<not> all_ok p lo hi n0 then False
      else if gterminal p dlf q N R Hb lo hi n0 band then True
      else let K = gcands p dlf q N R Hb lo hi n0 band in
        if (length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo
          then gverify p dlf q N IN n0f band Dmax wmin f lo (tc lo hi) \<sigma> \<and> gverify p dlf q N IN n0f band Dmax wmin f (tc lo hi) hi \<sigma>
        else if K = [] then True
        else if Dmax \<le> length \<sigma> then False
        else list_all (\<lambda>s. gverify p dlf q N IN n0f band Dmax wmin f lo hi (s # \<sigma>)) K)"

lemma length_gcorrs_le: "length (gcorrs p N dlv bd tm ts t n) \<le> n"
  by (induction n) auto

theorem gverify_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
  shows "gverify p dlf q N IN n0f band Dmax wmin f lo hi \<sigma> \<Longrightarrow> length \<sigma> \<le> Dmax \<Longrightarrow>
         real_of_float lo \<le> t \<Longrightarrow> t \<le> real_of_float hi \<Longrightarrow>
         gcorrs (fpos q) N (real_of_float dlf) bd tm ts t (length \<sigma>) = \<sigma> \<Longrightarrow>
         gstops_within (fpos q) N (real_of_float dlf) bd tm ts t Dmax"
proof (induction f arbitrary: lo hi \<sigma>)
  case 0 then show ?case by simp
next
  case (Suc f)
  note V = Suc.prems(1) and len = Suc.prems(2) and t = Suc.prems(3,4) and cs = Suc.prems(5)
  define dlv where "dlv = real_of_float dlf"
  define R where "R = Rref p q N IN \<sigma>"
  define Hb where "Hb = Hbref p q N IN \<sigma>"
  define n0 where "n0 = n0f lo hi"
  define K where "K = gcands p dlf q N R Hb lo hi n0 band"
  have nok: "node_ok q N \<sigma> R Hb" unfolding R_def Hb_def by (rule node_ok_Rref [OF IN])
  have ok: "all_ok p lo hi n0" using V by (auto simp: n0_def Let_def split: if_splits)
  then have okm: "\<And>m. m < M \<Longrightarrow> dist_ok p lo hi n0 m" by (simp add: all_ok_def)
  let ?c = "grun (fpos q) N dlv bd tm ts t (length \<sigma>)"
  have c_exc: "?c = exc (fpos q) N (c0 (fpos q) t) \<sigma>" by (simp add: grun_exc cs dlv_def)
  let ?E = "gelig (fpos q) N dlv bd tm ?c t"
  have stop_now: "?E = {} \<Longrightarrow> gstops_within (fpos q) N dlv bd tm ts t Dmax"
    using len by (auto simp: gstops_within_def)
  have next_cand: "?E \<noteq> {} \<Longrightarrow> ts (sel (fpos q) N ?c ?E) \<in> set K"
  proof -
    assume ne: "?E \<noteq> {}"
    have pk: "fpeaks (fpos q) N ?c \<noteq> {}" using ne gelig_empty_no_peaks by blast
    have m0: "tm (fmains (fpos q) N ?c t) \<in> fmains (fpos q) N ?c t" by (rule tm_fmains [OF tr pk])
    have "sel (fpos q) N ?c ?E \<noteq> {}" by (intro sel_nonempty ne finite_gelig)
    with tr have s: "ts (sel (fpos q) N ?c ?E) \<in> sel (fpos q) N ?c ?E"
      by (simp add: tie_rule_def finite_subset [OF sel_subset finite_gelig])
    let ?ce = "exc (fpos q) N (c0 (fpos q) t) \<sigma>"
    have "gcand p dlf q N R Hb lo hi n0 band (ts (sel (fpos q) N ?ce (geligible (fpos q) N dlv bd ?ce t (tm (fmains (fpos q) N ?ce t)))))"
      using GC_Classify.gsel_cand [OF nok okm t bd m0 [unfolded c_exc] s [unfolded gelig_def c_exc, unfolded dlv_def]]
      by (simp add: dlv_def)
    then have "gcand p dlf q N R Hb lo hi n0 band (ts (sel (fpos q) N ?c ?E))"
      unfolding gelig_def c_exc .
    then show ?thesis by (simp add: K_def gcands_def gcand_def PPg_def)
  qed
  show ?case
  proof (cases "gterminal p dlf q N R Hb lo hi n0 band")
    case True
    have "?E = {}"
    proof (cases "fpeaks (fpos q) N ?c = {}")
      case True then show ?thesis by (rule gelig_empty_no_peaks)
    next
      case False
      have m0: "tm (fmains (fpos q) N ?c t) \<in> fmains (fpos q) N ?c t" by (rule tm_fmains [OF tr False])
      let ?ce = "exc (fpos q) N (c0 (fpos q) t) \<sigma>"
      have "geligible (fpos q) N dlv bd ?ce t (tm (fmains (fpos q) N ?ce t)) = {}"
        using GC_Classify.gterminal_sound [OF nok okm t bd m0 [unfolded c_exc] True] by (simp add: dlv_def)
      then show ?thesis unfolding gelig_def c_exc .
    qed
    then show ?thesis unfolding dlv_def by (rule stop_now [unfolded dlv_def])
  next
    case nt: False
    show ?thesis
    proof (cases "(length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo")
      case True
      have both: "gverify p dlf q N IN n0f band Dmax wmin f lo (tc lo hi) \<sigma>" "gverify p dlf q N IN n0f band Dmax wmin f (tc lo hi) hi \<sigma>"
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
        then show ?thesis unfolding dlv_def by (rule stop_now [unfolded dlv_def])
      next
        case Kne: False
        have cap: "\<not> Dmax \<le> length \<sigma>"
          using V ok nt nosplit Kne unfolding gverify.simps Let_def R_def [symmetric] Hb_def [symmetric] n0_def [symmetric] K_def [symmetric]
          by (auto split: if_splits)
        have la: "list_all (\<lambda>s. gverify p dlf q N IN n0f band Dmax wmin f lo hi (s # \<sigma>)) K"
          using V ok nt nosplit Kne cap unfolding gverify.simps Let_def R_def [symmetric] Hb_def [symmetric] n0_def [symmetric] K_def [symmetric]
          by (auto split: if_splits)
        show ?thesis
        proof (cases "?E = {}")
          case True then show ?thesis unfolding dlv_def by (rule stop_now [unfolded dlv_def])
        next
          case False
          let ?s = "ts (sel (fpos q) N ?c ?E)"
          have sK: "?s \<in> set K" using next_cand [OF False] by simp
          have v': "gverify p dlf q N IN n0f band Dmax wmin f lo hi (?s # \<sigma>)"
            using la sK by (simp add: list_all_iff)
          have cs': "gcorrs (fpos q) N (real_of_float dlf) bd tm ts t (length (?s # \<sigma>)) = ?s # \<sigma>"
            using False cs by (simp add: dlv_def)
          show ?thesis using Suc.IH [OF v' _ t cs'] cap by simp
        qed
      qed
    qed
  qed
qed

end
