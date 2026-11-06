theory GOCX_nc_194
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3104: "goc_sub None 3104"
  by (goc_eval goc_nc_3104)

lemma goc_nc_3105: "goc_sub None 3105"
  by (goc_eval goc_nc_3105)

lemma goc_nc_3106: "goc_sub None 3106"
  by (goc_eval goc_nc_3106)

lemma goc_nc_3107: "goc_sub None 3107"
  by (goc_eval goc_nc_3107)

lemma goc_nc_3108: "goc_sub None 3108"
  by (goc_eval goc_nc_3108)

lemma goc_nc_3109: "goc_sub None 3109"
  by (goc_eval goc_nc_3109)

lemma goc_nc_3110: "goc_sub None 3110"
  by (goc_eval goc_nc_3110)

lemma goc_nc_3111: "goc_sub None 3111"
  by (goc_eval goc_nc_3111)

lemma goc_nc_3112: "goc_sub None 3112"
  by (goc_eval goc_nc_3112)

lemma goc_nc_3113: "goc_sub None 3113"
  by (goc_eval goc_nc_3113)

lemma goc_nc_3114: "goc_sub None 3114"
  by (goc_eval goc_nc_3114)

lemma goc_nc_3115: "goc_sub None 3115"
  by (goc_eval goc_nc_3115)

lemma goc_nc_3116: "goc_sub None 3116"
  by (goc_eval goc_nc_3116)

lemma goc_nc_3117: "goc_sub None 3117"
  by (goc_eval goc_nc_3117)

lemma goc_nc_3118: "goc_sub None 3118"
  by (goc_eval goc_nc_3118)

lemma goc_nc_3119: "goc_sub None 3119"
  by (goc_eval goc_nc_3119)

lemma gupt_nc_194: "[3104..<3120] = [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]"
  by (simp add: upt_rec)

lemma gsec_nc_194: "\<forall>j\<in>{16 * 194..<16 * 194 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 194..<16 * 194 + 16}"
  then have "j \<in> set [3104..<3120]" unfolding set_upt by simp
  then have "j \<in> set [3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]" unfolding gupt_nc_194 .
  then show "goc_sub None j" using goc_nc_3104 goc_nc_3105 goc_nc_3106 goc_nc_3107 goc_nc_3108 goc_nc_3109 goc_nc_3110 goc_nc_3111 goc_nc_3112 goc_nc_3113 goc_nc_3114 goc_nc_3115 goc_nc_3116 goc_nc_3117 goc_nc_3118 goc_nc_3119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
