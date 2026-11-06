theory OCX_nc_133
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2128: "oc_sub None 2128"
  by (oc_eval oc_nc_2128)

lemma oc_nc_2129: "oc_sub None 2129"
  by (oc_eval oc_nc_2129)

lemma oc_nc_2130: "oc_sub None 2130"
  by (oc_eval oc_nc_2130)

lemma oc_nc_2131: "oc_sub None 2131"
  by (oc_eval oc_nc_2131)

lemma oc_nc_2132: "oc_sub None 2132"
  by (oc_eval oc_nc_2132)

lemma oc_nc_2133: "oc_sub None 2133"
  by (oc_eval oc_nc_2133)

lemma oc_nc_2134: "oc_sub None 2134"
  by (oc_eval oc_nc_2134)

lemma oc_nc_2135: "oc_sub None 2135"
  by (oc_eval oc_nc_2135)

lemma oc_nc_2136: "oc_sub None 2136"
  by (oc_eval oc_nc_2136)

lemma oc_nc_2137: "oc_sub None 2137"
  by (oc_eval oc_nc_2137)

lemma oc_nc_2138: "oc_sub None 2138"
  by (oc_eval oc_nc_2138)

lemma oc_nc_2139: "oc_sub None 2139"
  by (oc_eval oc_nc_2139)

lemma oc_nc_2140: "oc_sub None 2140"
  by (oc_eval oc_nc_2140)

lemma oc_nc_2141: "oc_sub None 2141"
  by (oc_eval oc_nc_2141)

lemma oc_nc_2142: "oc_sub None 2142"
  by (oc_eval oc_nc_2142)

lemma oc_nc_2143: "oc_sub None 2143"
  by (oc_eval oc_nc_2143)

lemma upt_nc_133: "[2128..<2144] = [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]"
  by (simp add: upt_rec)

lemma sec_nc_133: "\<forall>j\<in>{16 * 133..<16 * 133 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 133..<16 * 133 + 16}"
  then have "j \<in> set [2128..<2144]" unfolding set_upt by simp
  then have "j \<in> set [2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143]" unfolding upt_nc_133 .
  then show "oc_sub None j" using oc_nc_2128 oc_nc_2129 oc_nc_2130 oc_nc_2131 oc_nc_2132 oc_nc_2133 oc_nc_2134 oc_nc_2135 oc_nc_2136 oc_nc_2137 oc_nc_2138 oc_nc_2139 oc_nc_2140 oc_nc_2141 oc_nc_2142 oc_nc_2143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
