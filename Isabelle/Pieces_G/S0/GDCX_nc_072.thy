theory GDCX_nc_072
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1152: "gdc_sub None 1152"
  by (gdc_eval gdc_nc_1152)

lemma gdc_nc_1153: "gdc_sub None 1153"
  by (gdc_eval gdc_nc_1153)

lemma gdc_nc_1154: "gdc_sub None 1154"
  by (gdc_eval gdc_nc_1154)

lemma gdc_nc_1155: "gdc_sub None 1155"
  by (gdc_eval gdc_nc_1155)

lemma gdc_nc_1156: "gdc_sub None 1156"
  by (gdc_eval gdc_nc_1156)

lemma gdc_nc_1157: "gdc_sub None 1157"
  by (gdc_eval gdc_nc_1157)

lemma gdc_nc_1158: "gdc_sub None 1158"
  by (gdc_eval gdc_nc_1158)

lemma gdc_nc_1159: "gdc_sub None 1159"
  by (gdc_eval gdc_nc_1159)

lemma gdc_nc_1160: "gdc_sub None 1160"
  by (gdc_eval gdc_nc_1160)

lemma gdc_nc_1161: "gdc_sub None 1161"
  by (gdc_eval gdc_nc_1161)

lemma gdc_nc_1162: "gdc_sub None 1162"
  by (gdc_eval gdc_nc_1162)

lemma gdc_nc_1163: "gdc_sub None 1163"
  by (gdc_eval gdc_nc_1163)

lemma gdc_nc_1164: "gdc_sub None 1164"
  by (gdc_eval gdc_nc_1164)

lemma gdc_nc_1165: "gdc_sub None 1165"
  by (gdc_eval gdc_nc_1165)

lemma gdc_nc_1166: "gdc_sub None 1166"
  by (gdc_eval gdc_nc_1166)

lemma gdc_nc_1167: "gdc_sub None 1167"
  by (gdc_eval gdc_nc_1167)

lemma gupt_nc_072: "[1152..<1168] = [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]"
  by (simp add: upt_rec)

lemma gsec_nc_072: "\<forall>j\<in>{16 * 72..<16 * 72 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 72..<16 * 72 + 16}"
  then have "j \<in> set [1152..<1168]" unfolding set_upt by simp
  then have "j \<in> set [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]" unfolding gupt_nc_072 .
  then show "gdc_sub None j" using gdc_nc_1152 gdc_nc_1153 gdc_nc_1154 gdc_nc_1155 gdc_nc_1156 gdc_nc_1157 gdc_nc_1158 gdc_nc_1159 gdc_nc_1160 gdc_nc_1161 gdc_nc_1162 gdc_nc_1163 gdc_nc_1164 gdc_nc_1165 gdc_nc_1166 gdc_nc_1167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
