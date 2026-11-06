theory GDCX_nc_071
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1136: "gdc_sub None 1136"
  by (gdc_eval gdc_nc_1136)

lemma gdc_nc_1137: "gdc_sub None 1137"
  by (gdc_eval gdc_nc_1137)

lemma gdc_nc_1138: "gdc_sub None 1138"
  by (gdc_eval gdc_nc_1138)

lemma gdc_nc_1139: "gdc_sub None 1139"
  by (gdc_eval gdc_nc_1139)

lemma gdc_nc_1140: "gdc_sub None 1140"
  by (gdc_eval gdc_nc_1140)

lemma gdc_nc_1141: "gdc_sub None 1141"
  by (gdc_eval gdc_nc_1141)

lemma gdc_nc_1142: "gdc_sub None 1142"
  by (gdc_eval gdc_nc_1142)

lemma gdc_nc_1143: "gdc_sub None 1143"
  by (gdc_eval gdc_nc_1143)

lemma gdc_nc_1144: "gdc_sub None 1144"
  by (gdc_eval gdc_nc_1144)

lemma gdc_nc_1145: "gdc_sub None 1145"
  by (gdc_eval gdc_nc_1145)

lemma gdc_nc_1146: "gdc_sub None 1146"
  by (gdc_eval gdc_nc_1146)

lemma gdc_nc_1147: "gdc_sub None 1147"
  by (gdc_eval gdc_nc_1147)

lemma gdc_nc_1148: "gdc_sub None 1148"
  by (gdc_eval gdc_nc_1148)

lemma gdc_nc_1149: "gdc_sub None 1149"
  by (gdc_eval gdc_nc_1149)

lemma gdc_nc_1150: "gdc_sub None 1150"
  by (gdc_eval gdc_nc_1150)

lemma gdc_nc_1151: "gdc_sub None 1151"
  by (gdc_eval gdc_nc_1151)

lemma gupt_nc_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma gsec_nc_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding gupt_nc_071 .
  then show "gdc_sub None j" using gdc_nc_1136 gdc_nc_1137 gdc_nc_1138 gdc_nc_1139 gdc_nc_1140 gdc_nc_1141 gdc_nc_1142 gdc_nc_1143 gdc_nc_1144 gdc_nc_1145 gdc_nc_1146 gdc_nc_1147 gdc_nc_1148 gdc_nc_1149 gdc_nc_1150 gdc_nc_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
