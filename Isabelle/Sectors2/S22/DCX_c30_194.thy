theory DCX_c30_194
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3104: "dc_sub dc_b30 3104"
  by (dc_eval dc_c30_3104)

lemma dc_c30_3105: "dc_sub dc_b30 3105"
  by (dc_eval dc_c30_3105)

lemma dc_c30_3106: "dc_sub dc_b30 3106"
  by (dc_eval dc_c30_3106)

lemma dc_c30_3107: "dc_sub dc_b30 3107"
  by (dc_eval dc_c30_3107)

lemma dc_c30_3108: "dc_sub dc_b30 3108"
  by (dc_eval dc_c30_3108)

lemma dc_c30_3109: "dc_sub dc_b30 3109"
  by (dc_eval dc_c30_3109)

lemma dc_c30_3110: "dc_sub dc_b30 3110"
  by (dc_eval dc_c30_3110)

lemma dc_c30_3111: "dc_sub dc_b30 3111"
  by (dc_eval dc_c30_3111)

lemma dc_c30_3112: "dc_sub dc_b30 3112"
  by (dc_eval dc_c30_3112)

lemma dc_c30_3113: "dc_sub dc_b30 3113"
  by (dc_eval dc_c30_3113)

lemma dc_c30_3114: "dc_sub dc_b30 3114"
  by (dc_eval dc_c30_3114)

lemma dc_c30_3115: "dc_sub dc_b30 3115"
  by (dc_eval dc_c30_3115)

lemma dc_c30_3116: "dc_sub dc_b30 3116"
  by (dc_eval dc_c30_3116)

lemma dc_c30_3117: "dc_sub dc_b30 3117"
  by (dc_eval dc_c30_3117)

lemma dc_c30_3118: "dc_sub dc_b30 3118"
  by (dc_eval dc_c30_3118)

lemma dc_c30_3119: "dc_sub dc_b30 3119"
  by (dc_eval dc_c30_3119)

lemma upt_c30_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma sec_c30_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding upt_c30_194 .
  then show "dc_sub dc_b30 j" using dc_c30_3104 dc_c30_3105 dc_c30_3106 dc_c30_3107 dc_c30_3108 dc_c30_3109 dc_c30_3110 dc_c30_3111 dc_c30_3112 dc_c30_3113 dc_c30_3114 dc_c30_3115 dc_c30_3116 dc_c30_3117 dc_c30_3118 dc_c30_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
