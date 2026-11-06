theory OCX_c30_072
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1152: "oc_sub oc_b30 1152"
  by (oc_eval oc_c30_1152)

lemma oc_c30_1153: "oc_sub oc_b30 1153"
  by (oc_eval oc_c30_1153)

lemma oc_c30_1154: "oc_sub oc_b30 1154"
  by (oc_eval oc_c30_1154)

lemma oc_c30_1155: "oc_sub oc_b30 1155"
  by (oc_eval oc_c30_1155)

lemma oc_c30_1156: "oc_sub oc_b30 1156"
  by (oc_eval oc_c30_1156)

lemma oc_c30_1157: "oc_sub oc_b30 1157"
  by (oc_eval oc_c30_1157)

lemma oc_c30_1158: "oc_sub oc_b30 1158"
  by (oc_eval oc_c30_1158)

lemma oc_c30_1159: "oc_sub oc_b30 1159"
  by (oc_eval oc_c30_1159)

lemma oc_c30_1160: "oc_sub oc_b30 1160"
  by (oc_eval oc_c30_1160)

lemma oc_c30_1161: "oc_sub oc_b30 1161"
  by (oc_eval oc_c30_1161)

lemma oc_c30_1162: "oc_sub oc_b30 1162"
  by (oc_eval oc_c30_1162)

lemma oc_c30_1163: "oc_sub oc_b30 1163"
  by (oc_eval oc_c30_1163)

lemma oc_c30_1164: "oc_sub oc_b30 1164"
  by (oc_eval oc_c30_1164)

lemma oc_c30_1165: "oc_sub oc_b30 1165"
  by (oc_eval oc_c30_1165)

lemma oc_c30_1166: "oc_sub oc_b30 1166"
  by (oc_eval oc_c30_1166)

lemma oc_c30_1167: "oc_sub oc_b30 1167"
  by (oc_eval oc_c30_1167)

lemma upt_c30_072: "[1152..<1168] = [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]"
  by (simp add: upt_rec)

lemma sec_c30_072: "\<forall>j\<in>{16 * 72..<16 * 72 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 72..<16 * 72 + 16}"
  then have "j \<in> set [1152..<1168]" unfolding set_upt by simp
  then have "j \<in> set [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]" unfolding upt_c30_072 .
  then show "oc_sub oc_b30 j" using oc_c30_1152 oc_c30_1153 oc_c30_1154 oc_c30_1155 oc_c30_1156 oc_c30_1157 oc_c30_1158 oc_c30_1159 oc_c30_1160 oc_c30_1161 oc_c30_1162 oc_c30_1163 oc_c30_1164 oc_c30_1165 oc_c30_1166 oc_c30_1167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
