theory GDCX_nc_133
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2128: "gdc_sub None 2128"
  by (gdc_eval gdc_nc_2128)

lemma gdc_nc_2129: "gdc_sub None 2129"
  by (gdc_eval gdc_nc_2129)

lemma gdc_nc_2130: "gdc_sub None 2130"
  by (gdc_eval gdc_nc_2130)

lemma gdc_nc_2131: "gdc_sub None 2131"
  by (gdc_eval gdc_nc_2131)

lemma gdc_nc_2132: "gdc_sub None 2132"
  by (gdc_eval gdc_nc_2132)

lemma gdc_nc_2133: "gdc_sub None 2133"
  by (gdc_eval gdc_nc_2133)

lemma gdc_nc_2134: "gdc_sub None 2134"
  by (gdc_eval gdc_nc_2134)

lemma gdc_nc_2135: "gdc_sub None 2135"
  by (gdc_eval gdc_nc_2135)

lemma gdc_nc_2136: "gdc_sub None 2136"
  by (gdc_eval gdc_nc_2136)

lemma gdc_nc_2137: "gdc_sub None 2137"
  by (gdc_eval gdc_nc_2137)

lemma gdc_nc_2138: "gdc_sub None 2138"
  by (gdc_eval gdc_nc_2138)

lemma gdc_nc_2139: "gdc_sub None 2139"
  by (gdc_eval gdc_nc_2139)

lemma gdc_nc_2140: "gdc_sub None 2140"
  by (gdc_eval gdc_nc_2140)

lemma gdc_nc_2141: "gdc_sub None 2141"
  by (gdc_eval gdc_nc_2141)

lemma gdc_nc_2142: "gdc_sub None 2142"
  by (gdc_eval gdc_nc_2142)

lemma gdc_nc_2143: "gdc_sub None 2143"
  by (gdc_eval gdc_nc_2143)

lemma gupt_nc_133: "[2128..<2144] = [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]"
  by (simp add: upt_rec)

lemma gsec_nc_133: "\<forall>j\<in>{16 * 133..<16 * 133 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 133..<16 * 133 + 16}"
  then have "j \<in> set [2128..<2144]" unfolding set_upt by simp
  then have "j \<in> set [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]" unfolding gupt_nc_133 .
  then show "gdc_sub None j" using gdc_nc_2128 gdc_nc_2129 gdc_nc_2130 gdc_nc_2131 gdc_nc_2132 gdc_nc_2133 gdc_nc_2134 gdc_nc_2135 gdc_nc_2136 gdc_nc_2137 gdc_nc_2138 gdc_nc_2139 gdc_nc_2140 gdc_nc_2141 gdc_nc_2142 gdc_nc_2143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
