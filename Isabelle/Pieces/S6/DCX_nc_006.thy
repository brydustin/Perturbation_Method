theory DCX_nc_006
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0096: "dc_sub None 96"
  by (dc_eval dc_nc_0096)

lemma dc_nc_0097: "dc_sub None 97"
  by (dc_eval dc_nc_0097)

lemma dc_nc_0098: "dc_sub None 98"
  by (dc_eval dc_nc_0098)

lemma dc_nc_0099: "dc_sub None 99"
  by (dc_eval dc_nc_0099)

lemma dc_nc_0100: "dc_sub None 100"
  by (dc_eval dc_nc_0100)

lemma dc_nc_0101: "dc_sub None 101"
  by (dc_eval dc_nc_0101)

lemma dc_nc_0102: "dc_sub None 102"
  by (dc_eval dc_nc_0102)

lemma dc_nc_0103: "dc_sub None 103"
  by (dc_eval dc_nc_0103)

lemma dc_nc_0104: "dc_sub None 104"
  by (dc_eval dc_nc_0104)

lemma dc_nc_0105: "dc_sub None 105"
  by (dc_eval dc_nc_0105)

lemma dc_nc_0106: "dc_sub None 106"
  by (dc_eval dc_nc_0106)

lemma dc_nc_0107: "dc_sub None 107"
  by (dc_eval dc_nc_0107)

lemma dc_nc_0108: "dc_sub None 108"
  by (dc_eval dc_nc_0108)

lemma dc_nc_0109: "dc_sub None 109"
  by (dc_eval dc_nc_0109)

lemma dc_nc_0110: "dc_sub None 110"
  by (dc_eval dc_nc_0110)

lemma dc_nc_0111: "dc_sub None 111"
  by (dc_eval dc_nc_0111)

lemma upt_nc_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma sec_nc_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding upt_nc_006 .
  then show "dc_sub None j" using dc_nc_0096 dc_nc_0097 dc_nc_0098 dc_nc_0099 dc_nc_0100 dc_nc_0101 dc_nc_0102 dc_nc_0103 dc_nc_0104 dc_nc_0105 dc_nc_0106 dc_nc_0107 dc_nc_0108 dc_nc_0109 dc_nc_0110 dc_nc_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
