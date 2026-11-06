theory OCX_c30_008
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0128: "oc_sub oc_b30 128"
  by (oc_eval oc_c30_0128)

lemma oc_c30_0129: "oc_sub oc_b30 129"
  by (oc_eval oc_c30_0129)

lemma oc_c30_0130: "oc_sub oc_b30 130"
  by (oc_eval oc_c30_0130)

lemma oc_c30_0131: "oc_sub oc_b30 131"
  by (oc_eval oc_c30_0131)

lemma oc_c30_0132: "oc_sub oc_b30 132"
  by (oc_eval oc_c30_0132)

lemma oc_c30_0133: "oc_sub oc_b30 133"
  by (oc_eval oc_c30_0133)

lemma oc_c30_0134: "oc_sub oc_b30 134"
  by (oc_eval oc_c30_0134)

lemma oc_c30_0135: "oc_sub oc_b30 135"
  by (oc_eval oc_c30_0135)

lemma oc_c30_0136: "oc_sub oc_b30 136"
  by (oc_eval oc_c30_0136)

lemma oc_c30_0137: "oc_sub oc_b30 137"
  by (oc_eval oc_c30_0137)

lemma oc_c30_0138: "oc_sub oc_b30 138"
  by (oc_eval oc_c30_0138)

lemma oc_c30_0139: "oc_sub oc_b30 139"
  by (oc_eval oc_c30_0139)

lemma oc_c30_0140: "oc_sub oc_b30 140"
  by (oc_eval oc_c30_0140)

lemma oc_c30_0141: "oc_sub oc_b30 141"
  by (oc_eval oc_c30_0141)

lemma oc_c30_0142: "oc_sub oc_b30 142"
  by (oc_eval oc_c30_0142)

lemma oc_c30_0143: "oc_sub oc_b30 143"
  by (oc_eval oc_c30_0143)

lemma upt_c30_008: "[128..<144] = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]"
  by (simp add: upt_rec)

lemma sec_c30_008: "\<forall>j\<in>{16 * 8..<16 * 8 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 8..<16 * 8 + 16}"
  then have "j \<in> set [128..<144]" unfolding set_upt by simp
  then have "j \<in> set [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]" unfolding upt_c30_008 .
  then show "oc_sub oc_b30 j" using oc_c30_0128 oc_c30_0129 oc_c30_0130 oc_c30_0131 oc_c30_0132 oc_c30_0133 oc_c30_0134 oc_c30_0135 oc_c30_0136 oc_c30_0137 oc_c30_0138 oc_c30_0139 oc_c30_0140 oc_c30_0141 oc_c30_0142 oc_c30_0143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
