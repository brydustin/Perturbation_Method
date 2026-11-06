theory DCX_c30_133
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2128: "dc_sub dc_b30 2128"
  by (dc_eval dc_c30_2128)

lemma dc_c30_2129: "dc_sub dc_b30 2129"
  by (dc_eval dc_c30_2129)

lemma dc_c30_2130: "dc_sub dc_b30 2130"
  by (dc_eval dc_c30_2130)

lemma dc_c30_2131: "dc_sub dc_b30 2131"
  by (dc_eval dc_c30_2131)

lemma dc_c30_2132: "dc_sub dc_b30 2132"
  by (dc_eval dc_c30_2132)

lemma dc_c30_2133: "dc_sub dc_b30 2133"
  by (dc_eval dc_c30_2133)

lemma dc_c30_2134: "dc_sub dc_b30 2134"
  by (dc_eval dc_c30_2134)

lemma dc_c30_2135: "dc_sub dc_b30 2135"
  by (dc_eval dc_c30_2135)

lemma dc_c30_2136: "dc_sub dc_b30 2136"
  by (dc_eval dc_c30_2136)

lemma dc_c30_2137: "dc_sub dc_b30 2137"
  by (dc_eval dc_c30_2137)

lemma dc_c30_2138: "dc_sub dc_b30 2138"
  by (dc_eval dc_c30_2138)

lemma dc_c30_2139: "dc_sub dc_b30 2139"
  by (dc_eval dc_c30_2139)

lemma dc_c30_2140: "dc_sub dc_b30 2140"
  by (dc_eval dc_c30_2140)

lemma dc_c30_2141: "dc_sub dc_b30 2141"
  by (dc_eval dc_c30_2141)

lemma dc_c30_2142: "dc_sub dc_b30 2142"
  by (dc_eval dc_c30_2142)

lemma dc_c30_2143: "dc_sub dc_b30 2143"
  by (dc_eval dc_c30_2143)

lemma upt_c30_133: "[2128..<2144] = [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]"
  by (simp add: upt_rec)

lemma sec_c30_133: "\<forall>j\<in>{16 * 133..<16 * 133 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 133..<16 * 133 + 16}"
  then have "j \<in> set [2128..<2144]" unfolding set_upt by simp
  then have "j \<in> set [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]" unfolding upt_c30_133 .
  then show "dc_sub dc_b30 j" using dc_c30_2128 dc_c30_2129 dc_c30_2130 dc_c30_2131 dc_c30_2132 dc_c30_2133 dc_c30_2134 dc_c30_2135 dc_c30_2136 dc_c30_2137 dc_c30_2138 dc_c30_2139 dc_c30_2140 dc_c30_2141 dc_c30_2142 dc_c30_2143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
