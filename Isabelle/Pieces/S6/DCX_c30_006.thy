theory DCX_c30_006
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0096: "dc_sub dc_b30 96"
  by (dc_eval dc_c30_0096)

lemma dc_c30_0097: "dc_sub dc_b30 97"
  by (dc_eval dc_c30_0097)

lemma dc_c30_0098: "dc_sub dc_b30 98"
  by (dc_eval dc_c30_0098)

lemma dc_c30_0099: "dc_sub dc_b30 99"
  by (dc_eval dc_c30_0099)

lemma dc_c30_0100: "dc_sub dc_b30 100"
  by (dc_eval dc_c30_0100)

lemma dc_c30_0101: "dc_sub dc_b30 101"
  by (dc_eval dc_c30_0101)

lemma dc_c30_0102: "dc_sub dc_b30 102"
  by (dc_eval dc_c30_0102)

lemma dc_c30_0103: "dc_sub dc_b30 103"
  by (dc_eval dc_c30_0103)

lemma dc_c30_0104: "dc_sub dc_b30 104"
  by (dc_eval dc_c30_0104)

lemma dc_c30_0105: "dc_sub dc_b30 105"
  by (dc_eval dc_c30_0105)

lemma dc_c30_0106: "dc_sub dc_b30 106"
  by (dc_eval dc_c30_0106)

lemma dc_c30_0107: "dc_sub dc_b30 107"
  by (dc_eval dc_c30_0107)

lemma dc_c30_0108: "dc_sub dc_b30 108"
  by (dc_eval dc_c30_0108)

lemma dc_c30_0109: "dc_sub dc_b30 109"
  by (dc_eval dc_c30_0109)

lemma dc_c30_0110: "dc_sub dc_b30 110"
  by (dc_eval dc_c30_0110)

lemma dc_c30_0111: "dc_sub dc_b30 111"
  by (dc_eval dc_c30_0111)

lemma upt_c30_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma sec_c30_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding upt_c30_006 .
  then show "dc_sub dc_b30 j" using dc_c30_0096 dc_c30_0097 dc_c30_0098 dc_c30_0099 dc_c30_0100 dc_c30_0101 dc_c30_0102 dc_c30_0103 dc_c30_0104 dc_c30_0105 dc_c30_0106 dc_c30_0107 dc_c30_0108 dc_c30_0109 dc_c30_0110 dc_c30_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
