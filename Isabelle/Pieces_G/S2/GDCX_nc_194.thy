theory GDCX_nc_194
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3104: "gdc_sub None 3104"
  by (gdc_eval gdc_nc_3104)

lemma gdc_nc_3105: "gdc_sub None 3105"
  by (gdc_eval gdc_nc_3105)

lemma gdc_nc_3106: "gdc_sub None 3106"
  by (gdc_eval gdc_nc_3106)

lemma gdc_nc_3107: "gdc_sub None 3107"
  by (gdc_eval gdc_nc_3107)

lemma gdc_nc_3108: "gdc_sub None 3108"
  by (gdc_eval gdc_nc_3108)

lemma gdc_nc_3109: "gdc_sub None 3109"
  by (gdc_eval gdc_nc_3109)

lemma gdc_nc_3110: "gdc_sub None 3110"
  by (gdc_eval gdc_nc_3110)

lemma gdc_nc_3111: "gdc_sub None 3111"
  by (gdc_eval gdc_nc_3111)

lemma gdc_nc_3112: "gdc_sub None 3112"
  by (gdc_eval gdc_nc_3112)

lemma gdc_nc_3113: "gdc_sub None 3113"
  by (gdc_eval gdc_nc_3113)

lemma gdc_nc_3114: "gdc_sub None 3114"
  by (gdc_eval gdc_nc_3114)

lemma gdc_nc_3115: "gdc_sub None 3115"
  by (gdc_eval gdc_nc_3115)

lemma gdc_nc_3116: "gdc_sub None 3116"
  by (gdc_eval gdc_nc_3116)

lemma gdc_nc_3117: "gdc_sub None 3117"
  by (gdc_eval gdc_nc_3117)

lemma gdc_nc_3118: "gdc_sub None 3118"
  by (gdc_eval gdc_nc_3118)

lemma gdc_nc_3119: "gdc_sub None 3119"
  by (gdc_eval gdc_nc_3119)

lemma gupt_nc_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma gsec_nc_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding gupt_nc_194 .
  then show "gdc_sub None j" using gdc_nc_3104 gdc_nc_3105 gdc_nc_3106 gdc_nc_3107 gdc_nc_3108 gdc_nc_3109 gdc_nc_3110 gdc_nc_3111 gdc_nc_3112 gdc_nc_3113 gdc_nc_3114 gdc_nc_3115 gdc_nc_3116 gdc_nc_3117 gdc_nc_3118 gdc_nc_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
