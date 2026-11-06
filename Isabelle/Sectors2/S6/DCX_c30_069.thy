theory DCX_c30_069
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1104: "dc_sub dc_b30 1104"
  by (dc_eval dc_c30_1104)

lemma dc_c30_1105: "dc_sub dc_b30 1105"
  by (dc_eval dc_c30_1105)

lemma dc_c30_1106: "dc_sub dc_b30 1106"
  by (dc_eval dc_c30_1106)

lemma dc_c30_1107: "dc_sub dc_b30 1107"
  by (dc_eval dc_c30_1107)

lemma dc_c30_1108: "dc_sub dc_b30 1108"
  by (dc_eval dc_c30_1108)

lemma dc_c30_1109: "dc_sub dc_b30 1109"
  by (dc_eval dc_c30_1109)

lemma dc_c30_1110: "dc_sub dc_b30 1110"
  by (dc_eval dc_c30_1110)

lemma dc_c30_1111: "dc_sub dc_b30 1111"
  by (dc_eval dc_c30_1111)

lemma dc_c30_1112: "dc_sub dc_b30 1112"
  by (dc_eval dc_c30_1112)

lemma dc_c30_1113: "dc_sub dc_b30 1113"
  by (dc_eval dc_c30_1113)

lemma dc_c30_1114: "dc_sub dc_b30 1114"
  by (dc_eval dc_c30_1114)

lemma dc_c30_1115: "dc_sub dc_b30 1115"
  by (dc_eval dc_c30_1115)

lemma dc_c30_1116: "dc_sub dc_b30 1116"
  by (dc_eval dc_c30_1116)

lemma dc_c30_1117: "dc_sub dc_b30 1117"
  by (dc_eval dc_c30_1117)

lemma dc_c30_1118: "dc_sub dc_b30 1118"
  by (dc_eval dc_c30_1118)

lemma dc_c30_1119: "dc_sub dc_b30 1119"
  by (dc_eval dc_c30_1119)

lemma upt_c30_069: "[1104..<1120] = [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]"
  by (simp add: upt_rec)

lemma sec_c30_069: "\<forall>j\<in>{16 * 69..<16 * 69 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 69..<16 * 69 + 16}"
  then have "j \<in> set [1104..<1120]" unfolding set_upt by simp
  then have "j \<in> set [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]" unfolding upt_c30_069 .
  then show "dc_sub dc_b30 j" using dc_c30_1104 dc_c30_1105 dc_c30_1106 dc_c30_1107 dc_c30_1108 dc_c30_1109 dc_c30_1110 dc_c30_1111 dc_c30_1112 dc_c30_1113 dc_c30_1114 dc_c30_1115 dc_c30_1116 dc_c30_1117 dc_c30_1118 dc_c30_1119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
