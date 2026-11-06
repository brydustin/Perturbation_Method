theory GDCX_nc_070
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1120: "gdc_sub None 1120"
  by (gdc_eval gdc_nc_1120)

lemma gdc_nc_1121: "gdc_sub None 1121"
  by (gdc_eval gdc_nc_1121)

lemma gdc_nc_1122: "gdc_sub None 1122"
  by (gdc_eval gdc_nc_1122)

lemma gdc_nc_1123: "gdc_sub None 1123"
  by (gdc_eval gdc_nc_1123)

lemma gdc_nc_1124: "gdc_sub None 1124"
  by (gdc_eval gdc_nc_1124)

lemma gdc_nc_1125: "gdc_sub None 1125"
  by (gdc_eval gdc_nc_1125)

lemma gdc_nc_1126: "gdc_sub None 1126"
  by (gdc_eval gdc_nc_1126)

lemma gdc_nc_1127: "gdc_sub None 1127"
  by (gdc_eval gdc_nc_1127)

lemma gdc_nc_1128: "gdc_sub None 1128"
  by (gdc_eval gdc_nc_1128)

lemma gdc_nc_1129: "gdc_sub None 1129"
  by (gdc_eval gdc_nc_1129)

lemma gdc_nc_1130: "gdc_sub None 1130"
  by (gdc_eval gdc_nc_1130)

lemma gdc_nc_1131: "gdc_sub None 1131"
  by (gdc_eval gdc_nc_1131)

lemma gdc_nc_1132: "gdc_sub None 1132"
  by (gdc_eval gdc_nc_1132)

lemma gdc_nc_1133: "gdc_sub None 1133"
  by (gdc_eval gdc_nc_1133)

lemma gdc_nc_1134: "gdc_sub None 1134"
  by (gdc_eval gdc_nc_1134)

lemma gdc_nc_1135: "gdc_sub None 1135"
  by (gdc_eval gdc_nc_1135)

lemma gupt_nc_070: "[1120..<1136] = [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]"
  by (simp add: upt_rec)

lemma gsec_nc_070: "\<forall>j\<in>{16 * 70..<16 * 70 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 70..<16 * 70 + 16}"
  then have "j \<in> set [1120..<1136]" unfolding set_upt by simp
  then have "j \<in> set [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]" unfolding gupt_nc_070 .
  then show "gdc_sub None j" using gdc_nc_1120 gdc_nc_1121 gdc_nc_1122 gdc_nc_1123 gdc_nc_1124 gdc_nc_1125 gdc_nc_1126 gdc_nc_1127 gdc_nc_1128 gdc_nc_1129 gdc_nc_1130 gdc_nc_1131 gdc_nc_1132 gdc_nc_1133 gdc_nc_1134 gdc_nc_1135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
