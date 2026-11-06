theory OCX_c30_068
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1088: "oc_sub oc_b30 1088"
  by (oc_eval oc_c30_1088)

lemma oc_c30_1089: "oc_sub oc_b30 1089"
  by (oc_eval oc_c30_1089)

lemma oc_c30_1090: "oc_sub oc_b30 1090"
  by (oc_eval oc_c30_1090)

lemma oc_c30_1091: "oc_sub oc_b30 1091"
  by (oc_eval oc_c30_1091)

lemma oc_c30_1092: "oc_sub oc_b30 1092"
  by (oc_eval oc_c30_1092)

lemma oc_c30_1093: "oc_sub oc_b30 1093"
  by (oc_eval oc_c30_1093)

lemma oc_c30_1094: "oc_sub oc_b30 1094"
  by (oc_eval oc_c30_1094)

lemma oc_c30_1095: "oc_sub oc_b30 1095"
  by (oc_eval oc_c30_1095)

lemma oc_c30_1096: "oc_sub oc_b30 1096"
  by (oc_eval oc_c30_1096)

lemma oc_c30_1097: "oc_sub oc_b30 1097"
  by (oc_eval oc_c30_1097)

lemma oc_c30_1098: "oc_sub oc_b30 1098"
  by (oc_eval oc_c30_1098)

lemma oc_c30_1099: "oc_sub oc_b30 1099"
  by (oc_eval oc_c30_1099)

lemma oc_c30_1100: "oc_sub oc_b30 1100"
  by (oc_eval oc_c30_1100)

lemma oc_c30_1101: "oc_sub oc_b30 1101"
  by (oc_eval oc_c30_1101)

lemma oc_c30_1102: "oc_sub oc_b30 1102"
  by (oc_eval oc_c30_1102)

lemma oc_c30_1103: "oc_sub oc_b30 1103"
  by (oc_eval oc_c30_1103)

lemma upt_c30_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma sec_c30_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding upt_c30_068 .
  then show "oc_sub oc_b30 j" using oc_c30_1088 oc_c30_1089 oc_c30_1090 oc_c30_1091 oc_c30_1092 oc_c30_1093 oc_c30_1094 oc_c30_1095 oc_c30_1096 oc_c30_1097 oc_c30_1098 oc_c30_1099 oc_c30_1100 oc_c30_1101 oc_c30_1102 oc_c30_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
