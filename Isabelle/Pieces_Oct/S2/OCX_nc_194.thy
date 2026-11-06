theory OCX_nc_194
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3104: "oc_sub None 3104"
  by (oc_eval oc_nc_3104)

lemma oc_nc_3105: "oc_sub None 3105"
  by (oc_eval oc_nc_3105)

lemma oc_nc_3106: "oc_sub None 3106"
  by (oc_eval oc_nc_3106)

lemma oc_nc_3107: "oc_sub None 3107"
  by (oc_eval oc_nc_3107)

lemma oc_nc_3108: "oc_sub None 3108"
  by (oc_eval oc_nc_3108)

lemma oc_nc_3109: "oc_sub None 3109"
  by (oc_eval oc_nc_3109)

lemma oc_nc_3110: "oc_sub None 3110"
  by (oc_eval oc_nc_3110)

lemma oc_nc_3111: "oc_sub None 3111"
  by (oc_eval oc_nc_3111)

lemma oc_nc_3112: "oc_sub None 3112"
  by (oc_eval oc_nc_3112)

lemma oc_nc_3113: "oc_sub None 3113"
  by (oc_eval oc_nc_3113)

lemma oc_nc_3114: "oc_sub None 3114"
  by (oc_eval oc_nc_3114)

lemma oc_nc_3115: "oc_sub None 3115"
  by (oc_eval oc_nc_3115)

lemma oc_nc_3116: "oc_sub None 3116"
  by (oc_eval oc_nc_3116)

lemma oc_nc_3117: "oc_sub None 3117"
  by (oc_eval oc_nc_3117)

lemma oc_nc_3118: "oc_sub None 3118"
  by (oc_eval oc_nc_3118)

lemma oc_nc_3119: "oc_sub None 3119"
  by (oc_eval oc_nc_3119)

lemma upt_nc_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma sec_nc_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding upt_nc_194 .
  then show "oc_sub None j" using oc_nc_3104 oc_nc_3105 oc_nc_3106 oc_nc_3107 oc_nc_3108 oc_nc_3109 oc_nc_3110 oc_nc_3111 oc_nc_3112 oc_nc_3113 oc_nc_3114 oc_nc_3115 oc_nc_3116 oc_nc_3117 oc_nc_3118 oc_nc_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
