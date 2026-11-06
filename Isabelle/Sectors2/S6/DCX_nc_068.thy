theory DCX_nc_068
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1088: "dc_sub None 1088"
  by (dc_eval dc_nc_1088)

lemma dc_nc_1089: "dc_sub None 1089"
  by (dc_eval dc_nc_1089)

lemma dc_nc_1090: "dc_sub None 1090"
  by (dc_eval dc_nc_1090)

lemma dc_nc_1091: "dc_sub None 1091"
  by (dc_eval dc_nc_1091)

lemma dc_nc_1092: "dc_sub None 1092"
  by (dc_eval dc_nc_1092)

lemma dc_nc_1093: "dc_sub None 1093"
  by (dc_eval dc_nc_1093)

lemma dc_nc_1094: "dc_sub None 1094"
  by (dc_eval dc_nc_1094)

lemma dc_nc_1095: "dc_sub None 1095"
  by (dc_eval dc_nc_1095)

lemma dc_nc_1096: "dc_sub None 1096"
  by (dc_eval dc_nc_1096)

lemma dc_nc_1097: "dc_sub None 1097"
  by (dc_eval dc_nc_1097)

lemma dc_nc_1098: "dc_sub None 1098"
  by (dc_eval dc_nc_1098)

lemma dc_nc_1099: "dc_sub None 1099"
  by (dc_eval dc_nc_1099)

lemma dc_nc_1100: "dc_sub None 1100"
  by (dc_eval dc_nc_1100)

lemma dc_nc_1101: "dc_sub None 1101"
  by (dc_eval dc_nc_1101)

lemma dc_nc_1102: "dc_sub None 1102"
  by (dc_eval dc_nc_1102)

lemma dc_nc_1103: "dc_sub None 1103"
  by (dc_eval dc_nc_1103)

lemma upt_nc_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma sec_nc_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding upt_nc_068 .
  then show "dc_sub None j" using dc_nc_1088 dc_nc_1089 dc_nc_1090 dc_nc_1091 dc_nc_1092 dc_nc_1093 dc_nc_1094 dc_nc_1095 dc_nc_1096 dc_nc_1097 dc_nc_1098 dc_nc_1099 dc_nc_1100 dc_nc_1101 dc_nc_1102 dc_nc_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
