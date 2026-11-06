theory GDCX_nc_131
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2096: "gdc_sub None 2096"
  by (gdc_eval gdc_nc_2096)

lemma gdc_nc_2097: "gdc_sub None 2097"
  by (gdc_eval gdc_nc_2097)

lemma gdc_nc_2098: "gdc_sub None 2098"
  by (gdc_eval gdc_nc_2098)

lemma gdc_nc_2099: "gdc_sub None 2099"
  by (gdc_eval gdc_nc_2099)

lemma gdc_nc_2100: "gdc_sub None 2100"
  by (gdc_eval gdc_nc_2100)

lemma gdc_nc_2101: "gdc_sub None 2101"
  by (gdc_eval gdc_nc_2101)

lemma gdc_nc_2102: "gdc_sub None 2102"
  by (gdc_eval gdc_nc_2102)

lemma gdc_nc_2103: "gdc_sub None 2103"
  by (gdc_eval gdc_nc_2103)

lemma gdc_nc_2104: "gdc_sub None 2104"
  by (gdc_eval gdc_nc_2104)

lemma gdc_nc_2105: "gdc_sub None 2105"
  by (gdc_eval gdc_nc_2105)

lemma gdc_nc_2106: "gdc_sub None 2106"
  by (gdc_eval gdc_nc_2106)

lemma gdc_nc_2107: "gdc_sub None 2107"
  by (gdc_eval gdc_nc_2107)

lemma gdc_nc_2108: "gdc_sub None 2108"
  by (gdc_eval gdc_nc_2108)

lemma gdc_nc_2109: "gdc_sub None 2109"
  by (gdc_eval gdc_nc_2109)

lemma gdc_nc_2110: "gdc_sub None 2110"
  by (gdc_eval gdc_nc_2110)

lemma gdc_nc_2111: "gdc_sub None 2111"
  by (gdc_eval gdc_nc_2111)

lemma gupt_nc_131: "[2096..<2112] = [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]"
  by (simp add: upt_rec)

lemma gsec_nc_131: "\<forall>j\<in>{16 * 131..<16 * 131 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 131..<16 * 131 + 16}"
  then have "j \<in> set [2096..<2112]" unfolding set_upt by simp
  then have "j \<in> set [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]" unfolding gupt_nc_131 .
  then show "gdc_sub None j" using gdc_nc_2096 gdc_nc_2097 gdc_nc_2098 gdc_nc_2099 gdc_nc_2100 gdc_nc_2101 gdc_nc_2102 gdc_nc_2103 gdc_nc_2104 gdc_nc_2105 gdc_nc_2106 gdc_nc_2107 gdc_nc_2108 gdc_nc_2109 gdc_nc_2110 gdc_nc_2111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
