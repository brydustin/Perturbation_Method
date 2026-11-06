theory OCX_c30_006
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0096: "oc_sub oc_b30 96"
  by (oc_eval oc_c30_0096)

lemma oc_c30_0097: "oc_sub oc_b30 97"
  by (oc_eval oc_c30_0097)

lemma oc_c30_0098: "oc_sub oc_b30 98"
  by (oc_eval oc_c30_0098)

lemma oc_c30_0099: "oc_sub oc_b30 99"
  by (oc_eval oc_c30_0099)

lemma oc_c30_0100: "oc_sub oc_b30 100"
  by (oc_eval oc_c30_0100)

lemma oc_c30_0101: "oc_sub oc_b30 101"
  by (oc_eval oc_c30_0101)

lemma oc_c30_0102: "oc_sub oc_b30 102"
  by (oc_eval oc_c30_0102)

lemma oc_c30_0103: "oc_sub oc_b30 103"
  by (oc_eval oc_c30_0103)

lemma oc_c30_0104: "oc_sub oc_b30 104"
  by (oc_eval oc_c30_0104)

lemma oc_c30_0105: "oc_sub oc_b30 105"
  by (oc_eval oc_c30_0105)

lemma oc_c30_0106: "oc_sub oc_b30 106"
  by (oc_eval oc_c30_0106)

lemma oc_c30_0107: "oc_sub oc_b30 107"
  by (oc_eval oc_c30_0107)

lemma oc_c30_0108: "oc_sub oc_b30 108"
  by (oc_eval oc_c30_0108)

lemma oc_c30_0109: "oc_sub oc_b30 109"
  by (oc_eval oc_c30_0109)

lemma oc_c30_0110: "oc_sub oc_b30 110"
  by (oc_eval oc_c30_0110)

lemma oc_c30_0111: "oc_sub oc_b30 111"
  by (oc_eval oc_c30_0111)

lemma upt_c30_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma sec_c30_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding upt_c30_006 .
  then show "oc_sub oc_b30 j" using oc_c30_0096 oc_c30_0097 oc_c30_0098 oc_c30_0099 oc_c30_0100 oc_c30_0101 oc_c30_0102 oc_c30_0103 oc_c30_0104 oc_c30_0105 oc_c30_0106 oc_c30_0107 oc_c30_0108 oc_c30_0109 oc_c30_0110 oc_c30_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
