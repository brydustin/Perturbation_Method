theory GOCX_nc_068
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1088: "goc_sub None 1088"
  by (goc_eval goc_nc_1088)

lemma goc_nc_1089: "goc_sub None 1089"
  by (goc_eval goc_nc_1089)

lemma goc_nc_1090: "goc_sub None 1090"
  by (goc_eval goc_nc_1090)

lemma goc_nc_1091: "goc_sub None 1091"
  by (goc_eval goc_nc_1091)

lemma goc_nc_1092: "goc_sub None 1092"
  by (goc_eval goc_nc_1092)

lemma goc_nc_1093: "goc_sub None 1093"
  by (goc_eval goc_nc_1093)

lemma goc_nc_1094: "goc_sub None 1094"
  by (goc_eval goc_nc_1094)

lemma goc_nc_1095: "goc_sub None 1095"
  by (goc_eval goc_nc_1095)

lemma goc_nc_1096: "goc_sub None 1096"
  by (goc_eval goc_nc_1096)

lemma goc_nc_1097: "goc_sub None 1097"
  by (goc_eval goc_nc_1097)

lemma goc_nc_1098: "goc_sub None 1098"
  by (goc_eval goc_nc_1098)

lemma goc_nc_1099: "goc_sub None 1099"
  by (goc_eval goc_nc_1099)

lemma goc_nc_1100: "goc_sub None 1100"
  by (goc_eval goc_nc_1100)

lemma goc_nc_1101: "goc_sub None 1101"
  by (goc_eval goc_nc_1101)

lemma goc_nc_1102: "goc_sub None 1102"
  by (goc_eval goc_nc_1102)

lemma goc_nc_1103: "goc_sub None 1103"
  by (goc_eval goc_nc_1103)

lemma gupt_nc_068: "[1088..<1104] = [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]"
  by (simp add: upt_rec)

lemma gsec_nc_068: "\<forall>j\<in>{16 * 68..<16 * 68 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 68..<16 * 68 + 16}"
  then have "j \<in> set [1088..<1104]" unfolding set_upt by simp
  then have "j \<in> set [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]" unfolding gupt_nc_068 .
  then show "goc_sub None j" using goc_nc_1088 goc_nc_1089 goc_nc_1090 goc_nc_1091 goc_nc_1092 goc_nc_1093 goc_nc_1094 goc_nc_1095 goc_nc_1096 goc_nc_1097 goc_nc_1098 goc_nc_1099 goc_nc_1100 goc_nc_1101 goc_nc_1102 goc_nc_1103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
