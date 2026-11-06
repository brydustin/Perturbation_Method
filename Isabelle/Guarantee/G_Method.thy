theory G_Method
  imports G_Pattern
begin

section \<open>The changed method\<close>

text \<open>Two changes to \<open>Algorithm\<close>.  A sample is a peak if it is at least as high as both
  neighbours and higher than one of them, so a flat top of two samples is seen; then the main
  peak's neighbours are excluded with it, since a flat main top has two peaks.  And the threshold
  is lowered by \<open>dl\<close>.\<close>

definition is_fpeak :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_fpeak p N c m \<longleftrightarrow> sq p N c m \<ge> sq p N c (prev_idx m) \<and> sq p N c m \<ge> sq p N c (next_idx m)
     \<and> (sq p N c m > sq p N c (prev_idx m) \<or> sq p N c m > sq p N c (next_idx m))"

definition fpeaks :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set" where
  "fpeaks p N c = {m. m < M \<and> is_fpeak p N c m}"

definition fmains :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "fmains p N c t = {m \<in> fpeaks p N c. \<forall>q \<in> fpeaks p N c. cdist (grid m) t \<le> cdist (grid q) t}"

definition geligible :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat \<Rightarrow> complex)
    \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set" where
  "geligible p N dl band c t m0 = {m \<in> fpeaks p N c. m \<noteq> m0 \<and> m \<noteq> prev_idx m0 \<and> m \<noteq> next_idx m0
      \<and> sq p N c m > sqmax p N c / 100 - dl \<and> in_band band t m}"

definition gelig :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "gelig p N dl band tm c t = geligible p N dl band c t (tm (fmains p N c t))"

primrec grun :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "grun p N dl band tm ts t 0 = c0 p t"
| "grun p N dl band tm ts t (Suc n) =
     (if gelig p N dl band tm (grun p N dl band tm ts t n) t = {} then grun p N dl band tm ts t n
      else corr p N (ts (sel p N (grun p N dl band tm ts t n) (gelig p N dl band tm (grun p N dl band tm ts t n) t)))
             (grun p N dl band tm ts t n))"

definition gstops_within :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "gstops_within p N dl band tm ts t D \<longleftrightarrow> (\<exists>n \<le> D. gelig p N dl band tm (grun p N dl band tm ts t n) t = {})"

lemma finite_fpeaks: "finite (fpeaks p N c)"
  by (simp add: fpeaks_def)

lemma fmains_nonempty:
  assumes "fpeaks p N c \<noteq> {}" shows "fmains p N c t \<noteq> {}"
proof -
  define d where "d = Min ((\<lambda>q. cdist (grid q) t) ` fpeaks p N c)"
  have "d \<in> (\<lambda>q. cdist (grid q) t) ` fpeaks p N c"
    unfolding d_def using assms finite_fpeaks by (intro Min_in) auto
  then obtain m where m: "m \<in> fpeaks p N c" "cdist (grid m) t = d" by auto
  have "d \<le> cdist (grid q) t" if "q \<in> fpeaks p N c" for q
    unfolding d_def using that finite_fpeaks by (intro Min_le) auto
  with m show ?thesis by (auto simp: fmains_def)
qed

text \<open>The main peak is a peak whenever there is one.\<close>
lemma main_in_fpeaks:
  assumes "tie_rule tm ts" "fpeaks p N c \<noteq> {}"
  shows "tm (fmains p N c t) \<in> fpeaks p N c"
proof -
  have "finite (fmains p N c t)"
    by (rule finite_subset [OF _ finite_fpeaks]) (auto simp: fmains_def)
  then have "tm (fmains p N c t) \<in> fmains p N c t"
    using assms fmains_nonempty [OF assms(2)] by (auto simp: tie_rule_def)
  then show ?thesis by (auto simp: fmains_def)
qed

text \<open>The norm of the weights never exceeds \<open>N\<close> along a run.\<close>
lemma nrm_grun: "nrm N (grun p N dl band tm ts t n) \<le> real N"
proof (induction n)
  case 0 then show ?case by (simp add: nrm_c0)
next
  case (Suc n)
  have "nrm N (grun p N dl band tm ts t (Suc n)) \<le> nrm N (grun p N dl band tm ts t n)"
    by (simp add: nrm_corr)
  with Suc.IH show ?case by linarith
qed

end
