theory GOCX_nc_072
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1152: "goc_sub None 1152"
  by (goc_eval goc_nc_1152)

lemma goc_nc_1153: "goc_sub None 1153"
  by (goc_eval goc_nc_1153)

lemma goc_nc_1154: "goc_sub None 1154"
  by (goc_eval goc_nc_1154)

lemma goc_nc_1155: "goc_sub None 1155"
  by (goc_eval goc_nc_1155)

lemma goc_nc_1156: "goc_sub None 1156"
  by (goc_eval goc_nc_1156)

lemma goc_nc_1157: "goc_sub None 1157"
  by (goc_eval goc_nc_1157)

lemma goc_nc_1158: "goc_sub None 1158"
  by (goc_eval goc_nc_1158)

lemma goc_nc_1159: "goc_sub None 1159"
  by (goc_eval goc_nc_1159)

lemma goc_nc_1160: "goc_sub None 1160"
  by (goc_eval goc_nc_1160)

lemma goc_nc_1161: "goc_sub None 1161"
  by (goc_eval goc_nc_1161)

lemma goc_nc_1162: "goc_sub None 1162"
  by (goc_eval goc_nc_1162)

lemma goc_nc_1163: "goc_sub None 1163"
  by (goc_eval goc_nc_1163)

lemma goc_nc_1164: "goc_sub None 1164"
  by (goc_eval goc_nc_1164)

lemma goc_nc_1165: "goc_sub None 1165"
  by (goc_eval goc_nc_1165)

lemma goc_nc_1166: "goc_sub None 1166"
  by (goc_eval goc_nc_1166)

lemma goc_nc_1167: "goc_sub None 1167"
  by (goc_eval goc_nc_1167)

lemma gupt_nc_072: "[1152..<1168] = [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]"
  by (simp add: upt_rec)

lemma gsec_nc_072: "\<forall>j\<in>{16 * 72..<16 * 72 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 72..<16 * 72 + 16}"
  then have "j \<in> set [1152..<1168]" unfolding set_upt by simp
  then have "j \<in> set [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]" unfolding gupt_nc_072 .
  then show "goc_sub None j" using goc_nc_1152 goc_nc_1153 goc_nc_1154 goc_nc_1155 goc_nc_1156 goc_nc_1157 goc_nc_1158 goc_nc_1159 goc_nc_1160 goc_nc_1161 goc_nc_1162 goc_nc_1163 goc_nc_1164 goc_nc_1165 goc_nc_1166 goc_nc_1167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
