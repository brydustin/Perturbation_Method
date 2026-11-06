theory DCX_c30_139
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2224: "dc_sub dc_b30 2224"
  by (dc_eval dc_c30_2224)

lemma dc_c30_2225: "dc_sub dc_b30 2225"
  by (dc_eval dc_c30_2225)

lemma dc_c30_2226: "dc_sub dc_b30 2226"
  by (dc_eval dc_c30_2226)

lemma dc_c30_2227: "dc_sub dc_b30 2227"
  by (dc_eval dc_c30_2227)

lemma dc_c30_2228: "dc_sub dc_b30 2228"
  by (dc_eval dc_c30_2228)

lemma dc_c30_2229: "dc_sub dc_b30 2229"
  by (dc_eval dc_c30_2229)

lemma dc_c30_2230: "dc_sub dc_b30 2230"
  by (dc_eval dc_c30_2230)

lemma dc_c30_2231: "dc_sub dc_b30 2231"
  by (dc_eval dc_c30_2231)

lemma dc_c30_2232: "dc_sub dc_b30 2232"
  by (dc_eval dc_c30_2232)

lemma dc_c30_2233: "dc_sub dc_b30 2233"
  by (dc_eval dc_c30_2233)

lemma dc_c30_2234: "dc_sub dc_b30 2234"
  by (dc_eval dc_c30_2234)

lemma dc_c30_2235: "dc_sub dc_b30 2235"
  by (dc_eval dc_c30_2235)

lemma dc_c30_2236: "dc_sub dc_b30 2236"
  by (dc_eval dc_c30_2236)

lemma dc_c30_2237: "dc_sub dc_b30 2237"
  by (dc_eval dc_c30_2237)

lemma dc_c30_2238: "dc_sub dc_b30 2238"
  by (dc_eval dc_c30_2238)

lemma dc_c30_2239: "dc_sub dc_b30 2239"
  by (dc_eval dc_c30_2239)

lemma upt_c30_139: "[2224..<2240] = [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]"
  by (simp add: upt_rec)

lemma sec_c30_139: "\<forall>j\<in>{16 * 139..<16 * 139 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 139..<16 * 139 + 16}"
  then have "j \<in> set [2224..<2240]" unfolding set_upt by simp
  then have "j \<in> set [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]" unfolding upt_c30_139 .
  then show "dc_sub dc_b30 j" using dc_c30_2224 dc_c30_2225 dc_c30_2226 dc_c30_2227 dc_c30_2228 dc_c30_2229 dc_c30_2230 dc_c30_2231 dc_c30_2232 dc_c30_2233 dc_c30_2234 dc_c30_2235 dc_c30_2236 dc_c30_2237 dc_c30_2238 dc_c30_2239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
