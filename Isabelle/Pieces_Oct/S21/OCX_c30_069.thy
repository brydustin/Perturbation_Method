theory OCX_c30_069
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1104: "oc_sub oc_b30 1104"
  by (oc_eval oc_c30_1104)

lemma oc_c30_1105: "oc_sub oc_b30 1105"
  by (oc_eval oc_c30_1105)

lemma oc_c30_1106: "oc_sub oc_b30 1106"
  by (oc_eval oc_c30_1106)

lemma oc_c30_1107: "oc_sub oc_b30 1107"
  by (oc_eval oc_c30_1107)

lemma oc_c30_1108: "oc_sub oc_b30 1108"
  by (oc_eval oc_c30_1108)

lemma oc_c30_1109: "oc_sub oc_b30 1109"
  by (oc_eval oc_c30_1109)

lemma oc_c30_1110: "oc_sub oc_b30 1110"
  by (oc_eval oc_c30_1110)

lemma oc_c30_1111: "oc_sub oc_b30 1111"
  by (oc_eval oc_c30_1111)

lemma oc_c30_1112: "oc_sub oc_b30 1112"
  by (oc_eval oc_c30_1112)

lemma oc_c30_1113: "oc_sub oc_b30 1113"
  by (oc_eval oc_c30_1113)

lemma oc_c30_1114: "oc_sub oc_b30 1114"
  by (oc_eval oc_c30_1114)

lemma oc_c30_1115: "oc_sub oc_b30 1115"
  by (oc_eval oc_c30_1115)

lemma oc_c30_1116: "oc_sub oc_b30 1116"
  by (oc_eval oc_c30_1116)

lemma oc_c30_1117: "oc_sub oc_b30 1117"
  by (oc_eval oc_c30_1117)

lemma oc_c30_1118: "oc_sub oc_b30 1118"
  by (oc_eval oc_c30_1118)

lemma oc_c30_1119: "oc_sub oc_b30 1119"
  by (oc_eval oc_c30_1119)

lemma upt_c30_069: "[1104..<1120] = [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]"
  by (simp add: upt_rec)

lemma sec_c30_069: "\<forall>j\<in>{16 * 69..<16 * 69 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 69..<16 * 69 + 16}"
  then have "j \<in> set [1104..<1120]" unfolding set_upt by simp
  then have "j \<in> set [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]" unfolding upt_c30_069 .
  then show "oc_sub oc_b30 j" using oc_c30_1104 oc_c30_1105 oc_c30_1106 oc_c30_1107 oc_c30_1108 oc_c30_1109 oc_c30_1110 oc_c30_1111 oc_c30_1112 oc_c30_1113 oc_c30_1114 oc_c30_1115 oc_c30_1116 oc_c30_1117 oc_c30_1118 oc_c30_1119
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
