theory DCX_nc_194
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3104: "dc_sub None 3104"
  by (dc_eval dc_nc_3104)

lemma dc_nc_3105: "dc_sub None 3105"
  by (dc_eval dc_nc_3105)

lemma dc_nc_3106: "dc_sub None 3106"
  by (dc_eval dc_nc_3106)

lemma dc_nc_3107: "dc_sub None 3107"
  by (dc_eval dc_nc_3107)

lemma dc_nc_3108: "dc_sub None 3108"
  by (dc_eval dc_nc_3108)

lemma dc_nc_3109: "dc_sub None 3109"
  by (dc_eval dc_nc_3109)

lemma dc_nc_3110: "dc_sub None 3110"
  by (dc_eval dc_nc_3110)

lemma dc_nc_3111: "dc_sub None 3111"
  by (dc_eval dc_nc_3111)

lemma dc_nc_3112: "dc_sub None 3112"
  by (dc_eval dc_nc_3112)

lemma dc_nc_3113: "dc_sub None 3113"
  by (dc_eval dc_nc_3113)

lemma dc_nc_3114: "dc_sub None 3114"
  by (dc_eval dc_nc_3114)

lemma dc_nc_3115: "dc_sub None 3115"
  by (dc_eval dc_nc_3115)

lemma dc_nc_3116: "dc_sub None 3116"
  by (dc_eval dc_nc_3116)

lemma dc_nc_3117: "dc_sub None 3117"
  by (dc_eval dc_nc_3117)

lemma dc_nc_3118: "dc_sub None 3118"
  by (dc_eval dc_nc_3118)

lemma dc_nc_3119: "dc_sub None 3119"
  by (dc_eval dc_nc_3119)

lemma upt_nc_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma sec_nc_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding upt_nc_194 .
  then show "dc_sub None j" using dc_nc_3104 dc_nc_3105 dc_nc_3106 dc_nc_3107 dc_nc_3108 dc_nc_3109 dc_nc_3110 dc_nc_3111 dc_nc_3112 dc_nc_3113 dc_nc_3114 dc_nc_3115 dc_nc_3116 dc_nc_3117 dc_nc_3118 dc_nc_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
