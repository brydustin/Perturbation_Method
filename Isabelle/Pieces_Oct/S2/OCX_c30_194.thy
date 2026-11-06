theory OCX_c30_194
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3104: "oc_sub oc_b30 3104"
  by (oc_eval oc_c30_3104)

lemma oc_c30_3105: "oc_sub oc_b30 3105"
  by (oc_eval oc_c30_3105)

lemma oc_c30_3106: "oc_sub oc_b30 3106"
  by (oc_eval oc_c30_3106)

lemma oc_c30_3107: "oc_sub oc_b30 3107"
  by (oc_eval oc_c30_3107)

lemma oc_c30_3108: "oc_sub oc_b30 3108"
  by (oc_eval oc_c30_3108)

lemma oc_c30_3109: "oc_sub oc_b30 3109"
  by (oc_eval oc_c30_3109)

lemma oc_c30_3110: "oc_sub oc_b30 3110"
  by (oc_eval oc_c30_3110)

lemma oc_c30_3111: "oc_sub oc_b30 3111"
  by (oc_eval oc_c30_3111)

lemma oc_c30_3112: "oc_sub oc_b30 3112"
  by (oc_eval oc_c30_3112)

lemma oc_c30_3113: "oc_sub oc_b30 3113"
  by (oc_eval oc_c30_3113)

lemma oc_c30_3114: "oc_sub oc_b30 3114"
  by (oc_eval oc_c30_3114)

lemma oc_c30_3115: "oc_sub oc_b30 3115"
  by (oc_eval oc_c30_3115)

lemma oc_c30_3116: "oc_sub oc_b30 3116"
  by (oc_eval oc_c30_3116)

lemma oc_c30_3117: "oc_sub oc_b30 3117"
  by (oc_eval oc_c30_3117)

lemma oc_c30_3118: "oc_sub oc_b30 3118"
  by (oc_eval oc_c30_3118)

lemma oc_c30_3119: "oc_sub oc_b30 3119"
  by (oc_eval oc_c30_3119)

lemma upt_c30_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma sec_c30_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding upt_c30_194 .
  then show "oc_sub oc_b30 j" using oc_c30_3104 oc_c30_3105 oc_c30_3106 oc_c30_3107 oc_c30_3108 oc_c30_3109 oc_c30_3110 oc_c30_3111 oc_c30_3112 oc_c30_3113 oc_c30_3114 oc_c30_3115 oc_c30_3116 oc_c30_3117 oc_c30_3118 oc_c30_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
