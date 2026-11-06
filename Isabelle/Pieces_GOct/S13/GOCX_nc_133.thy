theory GOCX_nc_133
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2128: "goc_sub None 2128"
  by (goc_eval goc_nc_2128)

lemma goc_nc_2129: "goc_sub None 2129"
  by (goc_eval goc_nc_2129)

lemma goc_nc_2130: "goc_sub None 2130"
  by (goc_eval goc_nc_2130)

lemma goc_nc_2131: "goc_sub None 2131"
  by (goc_eval goc_nc_2131)

lemma goc_nc_2132: "goc_sub None 2132"
  by (goc_eval goc_nc_2132)

lemma goc_nc_2133: "goc_sub None 2133"
  by (goc_eval goc_nc_2133)

lemma goc_nc_2134: "goc_sub None 2134"
  by (goc_eval goc_nc_2134)

lemma goc_nc_2135: "goc_sub None 2135"
  by (goc_eval goc_nc_2135)

lemma goc_nc_2136: "goc_sub None 2136"
  by (goc_eval goc_nc_2136)

lemma goc_nc_2137: "goc_sub None 2137"
  by (goc_eval goc_nc_2137)

lemma goc_nc_2138: "goc_sub None 2138"
  by (goc_eval goc_nc_2138)

lemma goc_nc_2139: "goc_sub None 2139"
  by (goc_eval goc_nc_2139)

lemma goc_nc_2140: "goc_sub None 2140"
  by (goc_eval goc_nc_2140)

lemma goc_nc_2141: "goc_sub None 2141"
  by (goc_eval goc_nc_2141)

lemma goc_nc_2142: "goc_sub None 2142"
  by (goc_eval goc_nc_2142)

lemma goc_nc_2143: "goc_sub None 2143"
  by (goc_eval goc_nc_2143)

lemma gupt_nc_133: "[2128..<2144] = [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]"
  by (simp add: upt_rec)

lemma gsec_nc_133: "\<forall>j\<in>{16 * 133..<16 * 133 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 133..<16 * 133 + 16}"
  then have "j \<in> set [2128..<2144]" unfolding set_upt by simp
  then have "j \<in> set [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]" unfolding gupt_nc_133 .
  then show "goc_sub None j" using goc_nc_2128 goc_nc_2129 goc_nc_2130 goc_nc_2131 goc_nc_2132 goc_nc_2133 goc_nc_2134 goc_nc_2135 goc_nc_2136 goc_nc_2137 goc_nc_2138 goc_nc_2139 goc_nc_2140 goc_nc_2141 goc_nc_2142 goc_nc_2143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
