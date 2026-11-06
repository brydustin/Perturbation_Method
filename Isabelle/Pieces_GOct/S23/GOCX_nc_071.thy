theory GOCX_nc_071
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1136: "goc_sub None 1136"
  by (goc_eval goc_nc_1136)

lemma goc_nc_1137: "goc_sub None 1137"
  by (goc_eval goc_nc_1137)

lemma goc_nc_1138: "goc_sub None 1138"
  by (goc_eval goc_nc_1138)

lemma goc_nc_1139: "goc_sub None 1139"
  by (goc_eval goc_nc_1139)

lemma goc_nc_1140: "goc_sub None 1140"
  by (goc_eval goc_nc_1140)

lemma goc_nc_1141: "goc_sub None 1141"
  by (goc_eval goc_nc_1141)

lemma goc_nc_1142: "goc_sub None 1142"
  by (goc_eval goc_nc_1142)

lemma goc_nc_1143: "goc_sub None 1143"
  by (goc_eval goc_nc_1143)

lemma goc_nc_1144: "goc_sub None 1144"
  by (goc_eval goc_nc_1144)

lemma goc_nc_1145: "goc_sub None 1145"
  by (goc_eval goc_nc_1145)

lemma goc_nc_1146: "goc_sub None 1146"
  by (goc_eval goc_nc_1146)

lemma goc_nc_1147: "goc_sub None 1147"
  by (goc_eval goc_nc_1147)

lemma goc_nc_1148: "goc_sub None 1148"
  by (goc_eval goc_nc_1148)

lemma goc_nc_1149: "goc_sub None 1149"
  by (goc_eval goc_nc_1149)

lemma goc_nc_1150: "goc_sub None 1150"
  by (goc_eval goc_nc_1150)

lemma goc_nc_1151: "goc_sub None 1151"
  by (goc_eval goc_nc_1151)

lemma gupt_nc_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma gsec_nc_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding gupt_nc_071 .
  then show "goc_sub None j" using goc_nc_1136 goc_nc_1137 goc_nc_1138 goc_nc_1139 goc_nc_1140 goc_nc_1141 goc_nc_1142 goc_nc_1143 goc_nc_1144 goc_nc_1145 goc_nc_1146 goc_nc_1147 goc_nc_1148 goc_nc_1149 goc_nc_1150 goc_nc_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
