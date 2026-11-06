theory DCX_c30_072
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1152: "dc_sub dc_b30 1152"
  by (dc_eval dc_c30_1152)

lemma dc_c30_1153: "dc_sub dc_b30 1153"
  by (dc_eval dc_c30_1153)

lemma dc_c30_1154: "dc_sub dc_b30 1154"
  by (dc_eval dc_c30_1154)

lemma dc_c30_1155: "dc_sub dc_b30 1155"
  by (dc_eval dc_c30_1155)

lemma dc_c30_1156: "dc_sub dc_b30 1156"
  by (dc_eval dc_c30_1156)

lemma dc_c30_1157: "dc_sub dc_b30 1157"
  by (dc_eval dc_c30_1157)

lemma dc_c30_1158: "dc_sub dc_b30 1158"
  by (dc_eval dc_c30_1158)

lemma dc_c30_1159: "dc_sub dc_b30 1159"
  by (dc_eval dc_c30_1159)

lemma dc_c30_1160: "dc_sub dc_b30 1160"
  by (dc_eval dc_c30_1160)

lemma dc_c30_1161: "dc_sub dc_b30 1161"
  by (dc_eval dc_c30_1161)

lemma dc_c30_1162: "dc_sub dc_b30 1162"
  by (dc_eval dc_c30_1162)

lemma dc_c30_1163: "dc_sub dc_b30 1163"
  by (dc_eval dc_c30_1163)

lemma dc_c30_1164: "dc_sub dc_b30 1164"
  by (dc_eval dc_c30_1164)

lemma dc_c30_1165: "dc_sub dc_b30 1165"
  by (dc_eval dc_c30_1165)

lemma dc_c30_1166: "dc_sub dc_b30 1166"
  by (dc_eval dc_c30_1166)

lemma dc_c30_1167: "dc_sub dc_b30 1167"
  by (dc_eval dc_c30_1167)

lemma upt_c30_072: "[1152..<1168] = [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]"
  by (simp add: upt_rec)

lemma sec_c30_072: "\<forall>j\<in>{16 * 72..<16 * 72 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 72..<16 * 72 + 16}"
  then have "j \<in> set [1152..<1168]" unfolding set_upt by simp
  then have "j \<in> set [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]" unfolding upt_c30_072 .
  then show "dc_sub dc_b30 j" using dc_c30_1152 dc_c30_1153 dc_c30_1154 dc_c30_1155 dc_c30_1156 dc_c30_1157 dc_c30_1158 dc_c30_1159 dc_c30_1160 dc_c30_1161 dc_c30_1162 dc_c30_1163 dc_c30_1164 dc_c30_1165 dc_c30_1166 dc_c30_1167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
