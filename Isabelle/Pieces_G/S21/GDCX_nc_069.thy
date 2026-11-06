theory GDCX_nc_069
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1104: "gdc_sub None 1104"
  by (gdc_eval gdc_nc_1104)

lemma gdc_nc_1105: "gdc_sub None 1105"
  by (gdc_eval gdc_nc_1105)

lemma gdc_nc_1106: "gdc_sub None 1106"
  by (gdc_eval gdc_nc_1106)

lemma gdc_nc_1107: "gdc_sub None 1107"
  by (gdc_eval gdc_nc_1107)

lemma gdc_nc_1108: "gdc_sub None 1108"
  by (gdc_eval gdc_nc_1108)

lemma gdc_nc_1109: "gdc_sub None 1109"
  by (gdc_eval gdc_nc_1109)

lemma gdc_nc_1110: "gdc_sub None 1110"
  by (gdc_eval gdc_nc_1110)

lemma gdc_nc_1111: "gdc_sub None 1111"
  by (gdc_eval gdc_nc_1111)

lemma gdc_nc_1112: "gdc_sub None 1112"
  by (gdc_eval gdc_nc_1112)

lemma gdc_nc_1113: "gdc_sub None 1113"
  by (gdc_eval gdc_nc_1113)

lemma gdc_nc_1114: "gdc_sub None 1114"
  by (gdc_eval gdc_nc_1114)

lemma gdc_nc_1115: "gdc_sub None 1115"
  by (gdc_eval gdc_nc_1115)

lemma gdc_nc_1116: "gdc_sub None 1116"
  by (gdc_eval gdc_nc_1116)

lemma gdc_nc_1117: "gdc_sub None 1117"
  by (gdc_eval gdc_nc_1117)

lemma gdc_nc_1118: "gdc_sub None 1118"
  by (gdc_eval gdc_nc_1118)

lemma gdc_nc_1119: "gdc_sub None 1119"
  by (gdc_eval gdc_nc_1119)

lemma gupt_nc_069: "[1104..<1120] = [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]"
  by (simp add: upt_rec)

lemma gsec_nc_069: "\<forall>j\<in>{16 * 69..<16 * 69 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 69..<16 * 69 + 16}"
  then have "j \<in> set [1104..<1120]" unfolding set_upt by simp
  then have "j \<in> set [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]" unfolding gupt_nc_069 .
  then show "gdc_sub None j" using gdc_nc_1104 gdc_nc_1105 gdc_nc_1106 gdc_nc_1107 gdc_nc_1108 gdc_nc_1109 gdc_nc_1110 gdc_nc_1111 gdc_nc_1112 gdc_nc_1113 gdc_nc_1114 gdc_nc_1115 gdc_nc_1116 gdc_nc_1117 gdc_nc_1118 gdc_nc_1119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
