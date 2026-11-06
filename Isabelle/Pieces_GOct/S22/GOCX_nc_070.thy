theory GOCX_nc_070
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1120: "goc_sub None 1120"
  by (goc_eval goc_nc_1120)

lemma goc_nc_1121: "goc_sub None 1121"
  by (goc_eval goc_nc_1121)

lemma goc_nc_1122: "goc_sub None 1122"
  by (goc_eval goc_nc_1122)

lemma goc_nc_1123: "goc_sub None 1123"
  by (goc_eval goc_nc_1123)

lemma goc_nc_1124: "goc_sub None 1124"
  by (goc_eval goc_nc_1124)

lemma goc_nc_1125: "goc_sub None 1125"
  by (goc_eval goc_nc_1125)

lemma goc_nc_1126: "goc_sub None 1126"
  by (goc_eval goc_nc_1126)

lemma goc_nc_1127: "goc_sub None 1127"
  by (goc_eval goc_nc_1127)

lemma goc_nc_1128: "goc_sub None 1128"
  by (goc_eval goc_nc_1128)

lemma goc_nc_1129: "goc_sub None 1129"
  by (goc_eval goc_nc_1129)

lemma goc_nc_1130: "goc_sub None 1130"
  by (goc_eval goc_nc_1130)

lemma goc_nc_1131: "goc_sub None 1131"
  by (goc_eval goc_nc_1131)

lemma goc_nc_1132: "goc_sub None 1132"
  by (goc_eval goc_nc_1132)

lemma goc_nc_1133: "goc_sub None 1133"
  by (goc_eval goc_nc_1133)

lemma goc_nc_1134: "goc_sub None 1134"
  by (goc_eval goc_nc_1134)

lemma goc_nc_1135: "goc_sub None 1135"
  by (goc_eval goc_nc_1135)

lemma gupt_nc_070: "[1120..<1136] = [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]"
  by (simp add: upt_rec)

lemma gsec_nc_070: "\<forall>j\<in>{16 * 70..<16 * 70 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 70..<16 * 70 + 16}"
  then have "j \<in> set [1120..<1136]" unfolding set_upt by simp
  then have "j \<in> set [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]" unfolding gupt_nc_070 .
  then show "goc_sub None j" using goc_nc_1120 goc_nc_1121 goc_nc_1122 goc_nc_1123 goc_nc_1124 goc_nc_1125 goc_nc_1126 goc_nc_1127 goc_nc_1128 goc_nc_1129 goc_nc_1130 goc_nc_1131 goc_nc_1132 goc_nc_1133 goc_nc_1134 goc_nc_1135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
