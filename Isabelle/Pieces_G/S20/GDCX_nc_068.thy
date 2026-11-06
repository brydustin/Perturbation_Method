theory GDCX_nc_068
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1088: "gdc_sub None 1088"
  by (gdc_eval gdc_nc_1088)

lemma gdc_nc_1089: "gdc_sub None 1089"
  by (gdc_eval gdc_nc_1089)

lemma gdc_nc_1090: "gdc_sub None 1090"
  by (gdc_eval gdc_nc_1090)

lemma gdc_nc_1091: "gdc_sub None 1091"
  by (gdc_eval gdc_nc_1091)

lemma gdc_nc_1092: "gdc_sub None 1092"
  by (gdc_eval gdc_nc_1092)

lemma gdc_nc_1093: "gdc_sub None 1093"
  by (gdc_eval gdc_nc_1093)

lemma gdc_nc_1094: "gdc_sub None 1094"
  by (gdc_eval gdc_nc_1094)

lemma gdc_nc_1095: "gdc_sub None 1095"
  by (gdc_eval gdc_nc_1095)

lemma gdc_nc_1096: "gdc_sub None 1096"
  by (gdc_eval gdc_nc_1096)

lemma gdc_nc_1097: "gdc_sub None 1097"
  by (gdc_eval gdc_nc_1097)

lemma gdc_nc_1098: "gdc_sub None 1098"
  by (gdc_eval gdc_nc_1098)

lemma gdc_nc_1099: "gdc_sub None 1099"
  by (gdc_eval gdc_nc_1099)

lemma gdc_nc_1100: "gdc_sub None 1100"
  by (gdc_eval gdc_nc_1100)

lemma gdc_nc_1101: "gdc_sub None 1101"
  by (gdc_eval gdc_nc_1101)

lemma gdc_nc_1102: "gdc_sub None 1102"
  by (gdc_eval gdc_nc_1102)

lemma gdc_nc_1103: "gdc_sub None 1103"
  by (gdc_eval gdc_nc_1103)

lemma gupt_nc_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma gsec_nc_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding gupt_nc_068 .
  then show "gdc_sub None j" using gdc_nc_1088 gdc_nc_1089 gdc_nc_1090 gdc_nc_1091 gdc_nc_1092 gdc_nc_1093 gdc_nc_1094 gdc_nc_1095 gdc_nc_1096 gdc_nc_1097 gdc_nc_1098 gdc_nc_1099 gdc_nc_1100 gdc_nc_1101 gdc_nc_1102 gdc_nc_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
