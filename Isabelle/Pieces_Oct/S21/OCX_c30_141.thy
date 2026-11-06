theory OCX_c30_141
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2256: "oc_sub oc_b30 2256"
  by (oc_eval oc_c30_2256)

lemma oc_c30_2257: "oc_sub oc_b30 2257"
  by (oc_eval oc_c30_2257)

lemma oc_c30_2258: "oc_sub oc_b30 2258"
  by (oc_eval oc_c30_2258)

lemma oc_c30_2259: "oc_sub oc_b30 2259"
  by (oc_eval oc_c30_2259)

lemma oc_c30_2260: "oc_sub oc_b30 2260"
  by (oc_eval oc_c30_2260)

lemma oc_c30_2261: "oc_sub oc_b30 2261"
  by (oc_eval oc_c30_2261)

lemma oc_c30_2262: "oc_sub oc_b30 2262"
  by (oc_eval oc_c30_2262)

lemma oc_c30_2263: "oc_sub oc_b30 2263"
  by (oc_eval oc_c30_2263)

lemma oc_c30_2264: "oc_sub oc_b30 2264"
  by (oc_eval oc_c30_2264)

lemma oc_c30_2265: "oc_sub oc_b30 2265"
  by (oc_eval oc_c30_2265)

lemma oc_c30_2266: "oc_sub oc_b30 2266"
  by (oc_eval oc_c30_2266)

lemma oc_c30_2267: "oc_sub oc_b30 2267"
  by (oc_eval oc_c30_2267)

lemma oc_c30_2268: "oc_sub oc_b30 2268"
  by (oc_eval oc_c30_2268)

lemma oc_c30_2269: "oc_sub oc_b30 2269"
  by (oc_eval oc_c30_2269)

lemma oc_c30_2270: "oc_sub oc_b30 2270"
  by (oc_eval oc_c30_2270)

lemma oc_c30_2271: "oc_sub oc_b30 2271"
  by (oc_eval oc_c30_2271)

lemma upt_c30_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma sec_c30_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding upt_c30_141 .
  then show "oc_sub oc_b30 j" using oc_c30_2256 oc_c30_2257 oc_c30_2258 oc_c30_2259 oc_c30_2260 oc_c30_2261 oc_c30_2262 oc_c30_2263 oc_c30_2264 oc_c30_2265 oc_c30_2266 oc_c30_2267 oc_c30_2268 oc_c30_2269 oc_c30_2270 oc_c30_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
