theory GOCX_nc_006
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0096: "goc_sub None 96"
  by (goc_eval goc_nc_0096)

lemma goc_nc_0097: "goc_sub None 97"
  by (goc_eval goc_nc_0097)

lemma goc_nc_0098: "goc_sub None 98"
  by (goc_eval goc_nc_0098)

lemma goc_nc_0099: "goc_sub None 99"
  by (goc_eval goc_nc_0099)

lemma goc_nc_0100: "goc_sub None 100"
  by (goc_eval goc_nc_0100)

lemma goc_nc_0101: "goc_sub None 101"
  by (goc_eval goc_nc_0101)

lemma goc_nc_0102: "goc_sub None 102"
  by (goc_eval goc_nc_0102)

lemma goc_nc_0103: "goc_sub None 103"
  by (goc_eval goc_nc_0103)

lemma goc_nc_0104: "goc_sub None 104"
  by (goc_eval goc_nc_0104)

lemma goc_nc_0105: "goc_sub None 105"
  by (goc_eval goc_nc_0105)

lemma goc_nc_0106: "goc_sub None 106"
  by (goc_eval goc_nc_0106)

lemma goc_nc_0107: "goc_sub None 107"
  by (goc_eval goc_nc_0107)

lemma goc_nc_0108: "goc_sub None 108"
  by (goc_eval goc_nc_0108)

lemma goc_nc_0109: "goc_sub None 109"
  by (goc_eval goc_nc_0109)

lemma goc_nc_0110: "goc_sub None 110"
  by (goc_eval goc_nc_0110)

lemma goc_nc_0111: "goc_sub None 111"
  by (goc_eval goc_nc_0111)

lemma gupt_nc_006: "[96..<112] = [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]"
  by (simp add: upt_rec)

lemma gsec_nc_006: "\<forall>j\<in>{16 * 6..<16 * 6 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 6..<16 * 6 + 16}"
  then have "j \<in> set [96..<112]" unfolding set_upt by simp
  then have "j \<in> set [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]" unfolding gupt_nc_006 .
  then show "goc_sub None j" using goc_nc_0096 goc_nc_0097 goc_nc_0098 goc_nc_0099 goc_nc_0100 goc_nc_0101 goc_nc_0102 goc_nc_0103 goc_nc_0104 goc_nc_0105 goc_nc_0106 goc_nc_0107 goc_nc_0108 goc_nc_0109 goc_nc_0110 goc_nc_0111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
