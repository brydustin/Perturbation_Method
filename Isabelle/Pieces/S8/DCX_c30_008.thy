theory DCX_c30_008
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0128: "dc_sub dc_b30 128"
  by (dc_eval dc_c30_0128)

lemma dc_c30_0129: "dc_sub dc_b30 129"
  by (dc_eval dc_c30_0129)

lemma dc_c30_0130: "dc_sub dc_b30 130"
  by (dc_eval dc_c30_0130)

lemma dc_c30_0131: "dc_sub dc_b30 131"
  by (dc_eval dc_c30_0131)

lemma dc_c30_0132: "dc_sub dc_b30 132"
  by (dc_eval dc_c30_0132)

lemma dc_c30_0133: "dc_sub dc_b30 133"
  by (dc_eval dc_c30_0133)

lemma dc_c30_0134: "dc_sub dc_b30 134"
  by (dc_eval dc_c30_0134)

lemma dc_c30_0135: "dc_sub dc_b30 135"
  by (dc_eval dc_c30_0135)

lemma dc_c30_0136: "dc_sub dc_b30 136"
  by (dc_eval dc_c30_0136)

lemma dc_c30_0137: "dc_sub dc_b30 137"
  by (dc_eval dc_c30_0137)

lemma dc_c30_0138: "dc_sub dc_b30 138"
  by (dc_eval dc_c30_0138)

lemma dc_c30_0139: "dc_sub dc_b30 139"
  by (dc_eval dc_c30_0139)

lemma dc_c30_0140: "dc_sub dc_b30 140"
  by (dc_eval dc_c30_0140)

lemma dc_c30_0141: "dc_sub dc_b30 141"
  by (dc_eval dc_c30_0141)

lemma dc_c30_0142: "dc_sub dc_b30 142"
  by (dc_eval dc_c30_0142)

lemma dc_c30_0143: "dc_sub dc_b30 143"
  by (dc_eval dc_c30_0143)

lemma upt_c30_008: "[128..<144] = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]"
  by (simp add: upt_rec)

lemma sec_c30_008: "\<forall>j\<in>{16 * 8..<16 * 8 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 8..<16 * 8 + 16}"
  then have "j \<in> set [128..<144]" unfolding set_upt by simp
  then have "j \<in> set [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]" unfolding upt_c30_008 .
  then show "dc_sub dc_b30 j" using dc_c30_0128 dc_c30_0129 dc_c30_0130 dc_c30_0131 dc_c30_0132 dc_c30_0133 dc_c30_0134 dc_c30_0135 dc_c30_0136 dc_c30_0137 dc_c30_0138 dc_c30_0139 dc_c30_0140 dc_c30_0141 dc_c30_0142 dc_c30_0143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
