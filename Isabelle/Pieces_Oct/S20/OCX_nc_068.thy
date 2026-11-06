theory OCX_nc_068
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1088: "oc_sub None 1088"
  by (oc_eval oc_nc_1088)

lemma oc_nc_1089: "oc_sub None 1089"
  by (oc_eval oc_nc_1089)

lemma oc_nc_1090: "oc_sub None 1090"
  by (oc_eval oc_nc_1090)

lemma oc_nc_1091: "oc_sub None 1091"
  by (oc_eval oc_nc_1091)

lemma oc_nc_1092: "oc_sub None 1092"
  by (oc_eval oc_nc_1092)

lemma oc_nc_1093: "oc_sub None 1093"
  by (oc_eval oc_nc_1093)

lemma oc_nc_1094: "oc_sub None 1094"
  by (oc_eval oc_nc_1094)

lemma oc_nc_1095: "oc_sub None 1095"
  by (oc_eval oc_nc_1095)

lemma oc_nc_1096: "oc_sub None 1096"
  by (oc_eval oc_nc_1096)

lemma oc_nc_1097: "oc_sub None 1097"
  by (oc_eval oc_nc_1097)

lemma oc_nc_1098: "oc_sub None 1098"
  by (oc_eval oc_nc_1098)

lemma oc_nc_1099: "oc_sub None 1099"
  by (oc_eval oc_nc_1099)

lemma oc_nc_1100: "oc_sub None 1100"
  by (oc_eval oc_nc_1100)

lemma oc_nc_1101: "oc_sub None 1101"
  by (oc_eval oc_nc_1101)

lemma oc_nc_1102: "oc_sub None 1102"
  by (oc_eval oc_nc_1102)

lemma oc_nc_1103: "oc_sub None 1103"
  by (oc_eval oc_nc_1103)

lemma upt_nc_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma sec_nc_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding upt_nc_068 .
  then show "oc_sub None j" using oc_nc_1088 oc_nc_1089 oc_nc_1090 oc_nc_1091 oc_nc_1092 oc_nc_1093 oc_nc_1094 oc_nc_1095 oc_nc_1096 oc_nc_1097 oc_nc_1098 oc_nc_1099 oc_nc_1100 oc_nc_1101 oc_nc_1102 oc_nc_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
