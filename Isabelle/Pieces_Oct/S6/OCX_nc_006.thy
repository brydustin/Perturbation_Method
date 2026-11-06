theory OCX_nc_006
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0096: "oc_sub None 96"
  by (oc_eval oc_nc_0096)

lemma oc_nc_0097: "oc_sub None 97"
  by (oc_eval oc_nc_0097)

lemma oc_nc_0098: "oc_sub None 98"
  by (oc_eval oc_nc_0098)

lemma oc_nc_0099: "oc_sub None 99"
  by (oc_eval oc_nc_0099)

lemma oc_nc_0100: "oc_sub None 100"
  by (oc_eval oc_nc_0100)

lemma oc_nc_0101: "oc_sub None 101"
  by (oc_eval oc_nc_0101)

lemma oc_nc_0102: "oc_sub None 102"
  by (oc_eval oc_nc_0102)

lemma oc_nc_0103: "oc_sub None 103"
  by (oc_eval oc_nc_0103)

lemma oc_nc_0104: "oc_sub None 104"
  by (oc_eval oc_nc_0104)

lemma oc_nc_0105: "oc_sub None 105"
  by (oc_eval oc_nc_0105)

lemma oc_nc_0106: "oc_sub None 106"
  by (oc_eval oc_nc_0106)

lemma oc_nc_0107: "oc_sub None 107"
  by (oc_eval oc_nc_0107)

lemma oc_nc_0108: "oc_sub None 108"
  by (oc_eval oc_nc_0108)

lemma oc_nc_0109: "oc_sub None 109"
  by (oc_eval oc_nc_0109)

lemma oc_nc_0110: "oc_sub None 110"
  by (oc_eval oc_nc_0110)

lemma oc_nc_0111: "oc_sub None 111"
  by (oc_eval oc_nc_0111)

lemma upt_nc_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma sec_nc_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding upt_nc_006 .
  then show "oc_sub None j" using oc_nc_0096 oc_nc_0097 oc_nc_0098 oc_nc_0099 oc_nc_0100 oc_nc_0101 oc_nc_0102 oc_nc_0103 oc_nc_0104 oc_nc_0105 oc_nc_0106 oc_nc_0107 oc_nc_0108 oc_nc_0109 oc_nc_0110 oc_nc_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
