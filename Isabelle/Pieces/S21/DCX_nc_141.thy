theory DCX_nc_141
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2256: "dc_sub None 2256"
  by (dc_eval dc_nc_2256)

lemma dc_nc_2257: "dc_sub None 2257"
  by (dc_eval dc_nc_2257)

lemma dc_nc_2258: "dc_sub None 2258"
  by (dc_eval dc_nc_2258)

lemma dc_nc_2259: "dc_sub None 2259"
  by (dc_eval dc_nc_2259)

lemma dc_nc_2260: "dc_sub None 2260"
  by (dc_eval dc_nc_2260)

lemma dc_nc_2261: "dc_sub None 2261"
  by (dc_eval dc_nc_2261)

lemma dc_nc_2262: "dc_sub None 2262"
  by (dc_eval dc_nc_2262)

lemma dc_nc_2263: "dc_sub None 2263"
  by (dc_eval dc_nc_2263)

lemma dc_nc_2264: "dc_sub None 2264"
  by (dc_eval dc_nc_2264)

lemma dc_nc_2265: "dc_sub None 2265"
  by (dc_eval dc_nc_2265)

lemma dc_nc_2266: "dc_sub None 2266"
  by (dc_eval dc_nc_2266)

lemma dc_nc_2267: "dc_sub None 2267"
  by (dc_eval dc_nc_2267)

lemma dc_nc_2268: "dc_sub None 2268"
  by (dc_eval dc_nc_2268)

lemma dc_nc_2269: "dc_sub None 2269"
  by (dc_eval dc_nc_2269)

lemma dc_nc_2270: "dc_sub None 2270"
  by (dc_eval dc_nc_2270)

lemma dc_nc_2271: "dc_sub None 2271"
  by (dc_eval dc_nc_2271)

lemma upt_nc_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma sec_nc_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding upt_nc_141 .
  then show "dc_sub None j" using dc_nc_2256 dc_nc_2257 dc_nc_2258 dc_nc_2259 dc_nc_2260 dc_nc_2261 dc_nc_2262 dc_nc_2263 dc_nc_2264 dc_nc_2265 dc_nc_2266 dc_nc_2267 dc_nc_2268 dc_nc_2269 dc_nc_2270 dc_nc_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
