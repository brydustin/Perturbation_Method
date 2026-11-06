theory OCX_nc_141
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2256: "oc_sub None 2256"
  by (oc_eval oc_nc_2256)

lemma oc_nc_2257: "oc_sub None 2257"
  by (oc_eval oc_nc_2257)

lemma oc_nc_2258: "oc_sub None 2258"
  by (oc_eval oc_nc_2258)

lemma oc_nc_2259: "oc_sub None 2259"
  by (oc_eval oc_nc_2259)

lemma oc_nc_2260: "oc_sub None 2260"
  by (oc_eval oc_nc_2260)

lemma oc_nc_2261: "oc_sub None 2261"
  by (oc_eval oc_nc_2261)

lemma oc_nc_2262: "oc_sub None 2262"
  by (oc_eval oc_nc_2262)

lemma oc_nc_2263: "oc_sub None 2263"
  by (oc_eval oc_nc_2263)

lemma oc_nc_2264: "oc_sub None 2264"
  by (oc_eval oc_nc_2264)

lemma oc_nc_2265: "oc_sub None 2265"
  by (oc_eval oc_nc_2265)

lemma oc_nc_2266: "oc_sub None 2266"
  by (oc_eval oc_nc_2266)

lemma oc_nc_2267: "oc_sub None 2267"
  by (oc_eval oc_nc_2267)

lemma oc_nc_2268: "oc_sub None 2268"
  by (oc_eval oc_nc_2268)

lemma oc_nc_2269: "oc_sub None 2269"
  by (oc_eval oc_nc_2269)

lemma oc_nc_2270: "oc_sub None 2270"
  by (oc_eval oc_nc_2270)

lemma oc_nc_2271: "oc_sub None 2271"
  by (oc_eval oc_nc_2271)

lemma upt_nc_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma sec_nc_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding upt_nc_141 .
  then show "oc_sub None j" using oc_nc_2256 oc_nc_2257 oc_nc_2258 oc_nc_2259 oc_nc_2260 oc_nc_2261 oc_nc_2262 oc_nc_2263 oc_nc_2264 oc_nc_2265 oc_nc_2266 oc_nc_2267 oc_nc_2268 oc_nc_2269 oc_nc_2270 oc_nc_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
