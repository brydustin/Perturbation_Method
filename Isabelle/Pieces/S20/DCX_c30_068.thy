theory DCX_c30_068
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1088: "dc_sub dc_b30 1088"
  by (dc_eval dc_c30_1088)

lemma dc_c30_1089: "dc_sub dc_b30 1089"
  by (dc_eval dc_c30_1089)

lemma dc_c30_1090: "dc_sub dc_b30 1090"
  by (dc_eval dc_c30_1090)

lemma dc_c30_1091: "dc_sub dc_b30 1091"
  by (dc_eval dc_c30_1091)

lemma dc_c30_1092: "dc_sub dc_b30 1092"
  by (dc_eval dc_c30_1092)

lemma dc_c30_1093: "dc_sub dc_b30 1093"
  by (dc_eval dc_c30_1093)

lemma dc_c30_1094: "dc_sub dc_b30 1094"
  by (dc_eval dc_c30_1094)

lemma dc_c30_1095: "dc_sub dc_b30 1095"
  by (dc_eval dc_c30_1095)

lemma dc_c30_1096: "dc_sub dc_b30 1096"
  by (dc_eval dc_c30_1096)

lemma dc_c30_1097: "dc_sub dc_b30 1097"
  by (dc_eval dc_c30_1097)

lemma dc_c30_1098: "dc_sub dc_b30 1098"
  by (dc_eval dc_c30_1098)

lemma dc_c30_1099: "dc_sub dc_b30 1099"
  by (dc_eval dc_c30_1099)

lemma dc_c30_1100: "dc_sub dc_b30 1100"
  by (dc_eval dc_c30_1100)

lemma dc_c30_1101: "dc_sub dc_b30 1101"
  by (dc_eval dc_c30_1101)

lemma dc_c30_1102: "dc_sub dc_b30 1102"
  by (dc_eval dc_c30_1102)

lemma dc_c30_1103: "dc_sub dc_b30 1103"
  by (dc_eval dc_c30_1103)

lemma upt_c30_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma sec_c30_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding upt_c30_068 .
  then show "dc_sub dc_b30 j" using dc_c30_1088 dc_c30_1089 dc_c30_1090 dc_c30_1091 dc_c30_1092 dc_c30_1093 dc_c30_1094 dc_c30_1095 dc_c30_1096 dc_c30_1097 dc_c30_1098 dc_c30_1099 dc_c30_1100 dc_c30_1101 dc_c30_1102 dc_c30_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
