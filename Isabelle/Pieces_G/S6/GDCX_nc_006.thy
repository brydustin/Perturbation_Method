theory GDCX_nc_006
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0096: "gdc_sub None 96"
  by (gdc_eval gdc_nc_0096)

lemma gdc_nc_0097: "gdc_sub None 97"
  by (gdc_eval gdc_nc_0097)

lemma gdc_nc_0098: "gdc_sub None 98"
  by (gdc_eval gdc_nc_0098)

lemma gdc_nc_0099: "gdc_sub None 99"
  by (gdc_eval gdc_nc_0099)

lemma gdc_nc_0100: "gdc_sub None 100"
  by (gdc_eval gdc_nc_0100)

lemma gdc_nc_0101: "gdc_sub None 101"
  by (gdc_eval gdc_nc_0101)

lemma gdc_nc_0102: "gdc_sub None 102"
  by (gdc_eval gdc_nc_0102)

lemma gdc_nc_0103: "gdc_sub None 103"
  by (gdc_eval gdc_nc_0103)

lemma gdc_nc_0104: "gdc_sub None 104"
  by (gdc_eval gdc_nc_0104)

lemma gdc_nc_0105: "gdc_sub None 105"
  by (gdc_eval gdc_nc_0105)

lemma gdc_nc_0106: "gdc_sub None 106"
  by (gdc_eval gdc_nc_0106)

lemma gdc_nc_0107: "gdc_sub None 107"
  by (gdc_eval gdc_nc_0107)

lemma gdc_nc_0108: "gdc_sub None 108"
  by (gdc_eval gdc_nc_0108)

lemma gdc_nc_0109: "gdc_sub None 109"
  by (gdc_eval gdc_nc_0109)

lemma gdc_nc_0110: "gdc_sub None 110"
  by (gdc_eval gdc_nc_0110)

lemma gdc_nc_0111: "gdc_sub None 111"
  by (gdc_eval gdc_nc_0111)

lemma gupt_nc_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma gsec_nc_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding gupt_nc_006 .
  then show "gdc_sub None j" using gdc_nc_0096 gdc_nc_0097 gdc_nc_0098 gdc_nc_0099 gdc_nc_0100 gdc_nc_0101 gdc_nc_0102 gdc_nc_0103 gdc_nc_0104 gdc_nc_0105 gdc_nc_0106 gdc_nc_0107 gdc_nc_0108 gdc_nc_0109 gdc_nc_0110 gdc_nc_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
