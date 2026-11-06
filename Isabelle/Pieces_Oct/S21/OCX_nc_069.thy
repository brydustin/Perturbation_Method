theory OCX_nc_069
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1104: "oc_sub None 1104"
  by (oc_eval oc_nc_1104)

lemma oc_nc_1105: "oc_sub None 1105"
  by (oc_eval oc_nc_1105)

lemma oc_nc_1106: "oc_sub None 1106"
  by (oc_eval oc_nc_1106)

lemma oc_nc_1107: "oc_sub None 1107"
  by (oc_eval oc_nc_1107)

lemma oc_nc_1108: "oc_sub None 1108"
  by (oc_eval oc_nc_1108)

lemma oc_nc_1109: "oc_sub None 1109"
  by (oc_eval oc_nc_1109)

lemma oc_nc_1110: "oc_sub None 1110"
  by (oc_eval oc_nc_1110)

lemma oc_nc_1111: "oc_sub None 1111"
  by (oc_eval oc_nc_1111)

lemma oc_nc_1112: "oc_sub None 1112"
  by (oc_eval oc_nc_1112)

lemma oc_nc_1113: "oc_sub None 1113"
  by (oc_eval oc_nc_1113)

lemma oc_nc_1114: "oc_sub None 1114"
  by (oc_eval oc_nc_1114)

lemma oc_nc_1115: "oc_sub None 1115"
  by (oc_eval oc_nc_1115)

lemma oc_nc_1116: "oc_sub None 1116"
  by (oc_eval oc_nc_1116)

lemma oc_nc_1117: "oc_sub None 1117"
  by (oc_eval oc_nc_1117)

lemma oc_nc_1118: "oc_sub None 1118"
  by (oc_eval oc_nc_1118)

lemma oc_nc_1119: "oc_sub None 1119"
  by (oc_eval oc_nc_1119)

lemma upt_nc_069: "[1104..<1120] = [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]"
  by (simp add: upt_rec)

lemma sec_nc_069: "\<forall>j\<in>{16 * 69..<16 * 69 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 69..<16 * 69 + 16}"
  then have "j \<in> set [1104..<1120]" unfolding set_upt by simp
  then have "j \<in> set [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]" unfolding upt_nc_069 .
  then show "oc_sub None j" using oc_nc_1104 oc_nc_1105 oc_nc_1106 oc_nc_1107 oc_nc_1108 oc_nc_1109 oc_nc_1110 oc_nc_1111 oc_nc_1112 oc_nc_1113 oc_nc_1114 oc_nc_1115 oc_nc_1116 oc_nc_1117 oc_nc_1118 oc_nc_1119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
