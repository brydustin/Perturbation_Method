theory GOCX_nc_069
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1104: "goc_sub None 1104"
  by (goc_eval goc_nc_1104)

lemma goc_nc_1105: "goc_sub None 1105"
  by (goc_eval goc_nc_1105)

lemma goc_nc_1106: "goc_sub None 1106"
  by (goc_eval goc_nc_1106)

lemma goc_nc_1107: "goc_sub None 1107"
  by (goc_eval goc_nc_1107)

lemma goc_nc_1108: "goc_sub None 1108"
  by (goc_eval goc_nc_1108)

lemma goc_nc_1109: "goc_sub None 1109"
  by (goc_eval goc_nc_1109)

lemma goc_nc_1110: "goc_sub None 1110"
  by (goc_eval goc_nc_1110)

lemma goc_nc_1111: "goc_sub None 1111"
  by (goc_eval goc_nc_1111)

lemma goc_nc_1112: "goc_sub None 1112"
  by (goc_eval goc_nc_1112)

lemma goc_nc_1113: "goc_sub None 1113"
  by (goc_eval goc_nc_1113)

lemma goc_nc_1114: "goc_sub None 1114"
  by (goc_eval goc_nc_1114)

lemma goc_nc_1115: "goc_sub None 1115"
  by (goc_eval goc_nc_1115)

lemma goc_nc_1116: "goc_sub None 1116"
  by (goc_eval goc_nc_1116)

lemma goc_nc_1117: "goc_sub None 1117"
  by (goc_eval goc_nc_1117)

lemma goc_nc_1118: "goc_sub None 1118"
  by (goc_eval goc_nc_1118)

lemma goc_nc_1119: "goc_sub None 1119"
  by (goc_eval goc_nc_1119)

lemma gupt_nc_069: "[1104..<1120] = [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]"
  by (simp add: upt_rec)

lemma gsec_nc_069: "\<forall>j\<in>{16 * 69..<16 * 69 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 69..<16 * 69 + 16}"
  then have "j \<in> set [1104..<1120]" unfolding set_upt by simp
  then have "j \<in> set [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]" unfolding gupt_nc_069 .
  then show "goc_sub None j" using goc_nc_1104 goc_nc_1105 goc_nc_1106 goc_nc_1107 goc_nc_1108 goc_nc_1109 goc_nc_1110 goc_nc_1111 goc_nc_1112 goc_nc_1113 goc_nc_1114 goc_nc_1115 goc_nc_1116 goc_nc_1117 goc_nc_1118 goc_nc_1119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
