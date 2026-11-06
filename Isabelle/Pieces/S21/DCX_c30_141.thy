theory DCX_c30_141
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2256: "dc_sub dc_b30 2256"
  by (dc_eval dc_c30_2256)

lemma dc_c30_2257: "dc_sub dc_b30 2257"
  by (dc_eval dc_c30_2257)

lemma dc_c30_2258: "dc_sub dc_b30 2258"
  by (dc_eval dc_c30_2258)

lemma dc_c30_2259: "dc_sub dc_b30 2259"
  by (dc_eval dc_c30_2259)

lemma dc_c30_2260: "dc_sub dc_b30 2260"
  by (dc_eval dc_c30_2260)

lemma dc_c30_2261: "dc_sub dc_b30 2261"
  by (dc_eval dc_c30_2261)

lemma dc_c30_2262: "dc_sub dc_b30 2262"
  by (dc_eval dc_c30_2262)

lemma dc_c30_2263: "dc_sub dc_b30 2263"
  by (dc_eval dc_c30_2263)

lemma dc_c30_2264: "dc_sub dc_b30 2264"
  by (dc_eval dc_c30_2264)

lemma dc_c30_2265: "dc_sub dc_b30 2265"
  by (dc_eval dc_c30_2265)

lemma dc_c30_2266: "dc_sub dc_b30 2266"
  by (dc_eval dc_c30_2266)

lemma dc_c30_2267: "dc_sub dc_b30 2267"
  by (dc_eval dc_c30_2267)

lemma dc_c30_2268: "dc_sub dc_b30 2268"
  by (dc_eval dc_c30_2268)

lemma dc_c30_2269: "dc_sub dc_b30 2269"
  by (dc_eval dc_c30_2269)

lemma dc_c30_2270: "dc_sub dc_b30 2270"
  by (dc_eval dc_c30_2270)

lemma dc_c30_2271: "dc_sub dc_b30 2271"
  by (dc_eval dc_c30_2271)

lemma upt_c30_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma sec_c30_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding upt_c30_141 .
  then show "dc_sub dc_b30 j" using dc_c30_2256 dc_c30_2257 dc_c30_2258 dc_c30_2259 dc_c30_2260 dc_c30_2261 dc_c30_2262 dc_c30_2263 dc_c30_2264 dc_c30_2265 dc_c30_2266 dc_c30_2267 dc_c30_2268 dc_c30_2269 dc_c30_2270 dc_c30_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
