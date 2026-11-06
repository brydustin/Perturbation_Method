theory DCX_c30_138
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2208: "dc_sub dc_b30 2208"
  by (dc_eval dc_c30_2208)

lemma dc_c30_2209: "dc_sub dc_b30 2209"
  by (dc_eval dc_c30_2209)

lemma dc_c30_2210: "dc_sub dc_b30 2210"
  by (dc_eval dc_c30_2210)

lemma dc_c30_2211: "dc_sub dc_b30 2211"
  by (dc_eval dc_c30_2211)

lemma dc_c30_2212: "dc_sub dc_b30 2212"
  by (dc_eval dc_c30_2212)

lemma dc_c30_2213: "dc_sub dc_b30 2213"
  by (dc_eval dc_c30_2213)

lemma dc_c30_2214: "dc_sub dc_b30 2214"
  by (dc_eval dc_c30_2214)

lemma dc_c30_2215: "dc_sub dc_b30 2215"
  by (dc_eval dc_c30_2215)

lemma dc_c30_2216: "dc_sub dc_b30 2216"
  by (dc_eval dc_c30_2216)

lemma dc_c30_2217: "dc_sub dc_b30 2217"
  by (dc_eval dc_c30_2217)

lemma dc_c30_2218: "dc_sub dc_b30 2218"
  by (dc_eval dc_c30_2218)

lemma dc_c30_2219: "dc_sub dc_b30 2219"
  by (dc_eval dc_c30_2219)

lemma dc_c30_2220: "dc_sub dc_b30 2220"
  by (dc_eval dc_c30_2220)

lemma dc_c30_2221: "dc_sub dc_b30 2221"
  by (dc_eval dc_c30_2221)

lemma dc_c30_2222: "dc_sub dc_b30 2222"
  by (dc_eval dc_c30_2222)

lemma dc_c30_2223: "dc_sub dc_b30 2223"
  by (dc_eval dc_c30_2223)

lemma upt_c30_138: "[2208..<2224] = [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]"
  by (simp add: upt_rec)

lemma sec_c30_138: "\<forall>j\<in>{16 * 138..<16 * 138 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 138..<16 * 138 + 16}"
  then have "j \<in> set [2208..<2224]" unfolding set_upt by simp
  then have "j \<in> set [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]" unfolding upt_c30_138 .
  then show "dc_sub dc_b30 j" using dc_c30_2208 dc_c30_2209 dc_c30_2210 dc_c30_2211 dc_c30_2212 dc_c30_2213 dc_c30_2214 dc_c30_2215 dc_c30_2216 dc_c30_2217 dc_c30_2218 dc_c30_2219 dc_c30_2220 dc_c30_2221 dc_c30_2222 dc_c30_2223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
