theory DCX_nc_133
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2128: "dc_sub None 2128"
  by (dc_eval dc_nc_2128)

lemma dc_nc_2129: "dc_sub None 2129"
  by (dc_eval dc_nc_2129)

lemma dc_nc_2130: "dc_sub None 2130"
  by (dc_eval dc_nc_2130)

lemma dc_nc_2131: "dc_sub None 2131"
  by (dc_eval dc_nc_2131)

lemma dc_nc_2132: "dc_sub None 2132"
  by (dc_eval dc_nc_2132)

lemma dc_nc_2133: "dc_sub None 2133"
  by (dc_eval dc_nc_2133)

lemma dc_nc_2134: "dc_sub None 2134"
  by (dc_eval dc_nc_2134)

lemma dc_nc_2135: "dc_sub None 2135"
  by (dc_eval dc_nc_2135)

lemma dc_nc_2136: "dc_sub None 2136"
  by (dc_eval dc_nc_2136)

lemma dc_nc_2137: "dc_sub None 2137"
  by (dc_eval dc_nc_2137)

lemma dc_nc_2138: "dc_sub None 2138"
  by (dc_eval dc_nc_2138)

lemma dc_nc_2139: "dc_sub None 2139"
  by (dc_eval dc_nc_2139)

lemma dc_nc_2140: "dc_sub None 2140"
  by (dc_eval dc_nc_2140)

lemma dc_nc_2141: "dc_sub None 2141"
  by (dc_eval dc_nc_2141)

lemma dc_nc_2142: "dc_sub None 2142"
  by (dc_eval dc_nc_2142)

lemma dc_nc_2143: "dc_sub None 2143"
  by (dc_eval dc_nc_2143)

lemma upt_nc_133: "[2128..<2144] = [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]"
  by (simp add: upt_rec)

lemma sec_nc_133: "\<forall>j\<in>{16 * 133..<16 * 133 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 133..<16 * 133 + 16}"
  then have "j \<in> set [2128..<2144]" unfolding set_upt by simp
  then have "j \<in> set [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]" unfolding upt_nc_133 .
  then show "dc_sub None j" using dc_nc_2128 dc_nc_2129 dc_nc_2130 dc_nc_2131 dc_nc_2132 dc_nc_2133 dc_nc_2134 dc_nc_2135 dc_nc_2136 dc_nc_2137 dc_nc_2138 dc_nc_2139 dc_nc_2140 dc_nc_2141 dc_nc_2142 dc_nc_2143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
