theory OCX_nc_072
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1152: "oc_sub None 1152"
  by (oc_eval oc_nc_1152)

lemma oc_nc_1153: "oc_sub None 1153"
  by (oc_eval oc_nc_1153)

lemma oc_nc_1154: "oc_sub None 1154"
  by (oc_eval oc_nc_1154)

lemma oc_nc_1155: "oc_sub None 1155"
  by (oc_eval oc_nc_1155)

lemma oc_nc_1156: "oc_sub None 1156"
  by (oc_eval oc_nc_1156)

lemma oc_nc_1157: "oc_sub None 1157"
  by (oc_eval oc_nc_1157)

lemma oc_nc_1158: "oc_sub None 1158"
  by (oc_eval oc_nc_1158)

lemma oc_nc_1159: "oc_sub None 1159"
  by (oc_eval oc_nc_1159)

lemma oc_nc_1160: "oc_sub None 1160"
  by (oc_eval oc_nc_1160)

lemma oc_nc_1161: "oc_sub None 1161"
  by (oc_eval oc_nc_1161)

lemma oc_nc_1162: "oc_sub None 1162"
  by (oc_eval oc_nc_1162)

lemma oc_nc_1163: "oc_sub None 1163"
  by (oc_eval oc_nc_1163)

lemma oc_nc_1164: "oc_sub None 1164"
  by (oc_eval oc_nc_1164)

lemma oc_nc_1165: "oc_sub None 1165"
  by (oc_eval oc_nc_1165)

lemma oc_nc_1166: "oc_sub None 1166"
  by (oc_eval oc_nc_1166)

lemma oc_nc_1167: "oc_sub None 1167"
  by (oc_eval oc_nc_1167)

lemma upt_nc_072: "[1152..<1168] = [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]"
  by (simp add: upt_rec)

lemma sec_nc_072: "\<forall>j\<in>{16 * 72..<16 * 72 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 72..<16 * 72 + 16}"
  then have "j \<in> set [1152..<1168]" unfolding set_upt by simp
  then have "j \<in> set [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]" unfolding upt_nc_072 .
  then show "oc_sub None j" using oc_nc_1152 oc_nc_1153 oc_nc_1154 oc_nc_1155 oc_nc_1156 oc_nc_1157 oc_nc_1158 oc_nc_1159 oc_nc_1160 oc_nc_1161 oc_nc_1162 oc_nc_1163 oc_nc_1164 oc_nc_1165 oc_nc_1166 oc_nc_1167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
