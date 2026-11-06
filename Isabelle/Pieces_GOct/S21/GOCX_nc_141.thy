theory GOCX_nc_141
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2256: "goc_sub None 2256"
  by (goc_eval goc_nc_2256)

lemma goc_nc_2257: "goc_sub None 2257"
  by (goc_eval goc_nc_2257)

lemma goc_nc_2258: "goc_sub None 2258"
  by (goc_eval goc_nc_2258)

lemma goc_nc_2259: "goc_sub None 2259"
  by (goc_eval goc_nc_2259)

lemma goc_nc_2260: "goc_sub None 2260"
  by (goc_eval goc_nc_2260)

lemma goc_nc_2261: "goc_sub None 2261"
  by (goc_eval goc_nc_2261)

lemma goc_nc_2262: "goc_sub None 2262"
  by (goc_eval goc_nc_2262)

lemma goc_nc_2263: "goc_sub None 2263"
  by (goc_eval goc_nc_2263)

lemma goc_nc_2264: "goc_sub None 2264"
  by (goc_eval goc_nc_2264)

lemma goc_nc_2265: "goc_sub None 2265"
  by (goc_eval goc_nc_2265)

lemma goc_nc_2266: "goc_sub None 2266"
  by (goc_eval goc_nc_2266)

lemma goc_nc_2267: "goc_sub None 2267"
  by (goc_eval goc_nc_2267)

lemma goc_nc_2268: "goc_sub None 2268"
  by (goc_eval goc_nc_2268)

lemma goc_nc_2269: "goc_sub None 2269"
  by (goc_eval goc_nc_2269)

lemma goc_nc_2270: "goc_sub None 2270"
  by (goc_eval goc_nc_2270)

lemma goc_nc_2271: "goc_sub None 2271"
  by (goc_eval goc_nc_2271)

lemma gupt_nc_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma gsec_nc_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding gupt_nc_141 .
  then show "goc_sub None j" using goc_nc_2256 goc_nc_2257 goc_nc_2258 goc_nc_2259 goc_nc_2260 goc_nc_2261 goc_nc_2262 goc_nc_2263 goc_nc_2264 goc_nc_2265 goc_nc_2266 goc_nc_2267 goc_nc_2268 goc_nc_2269 goc_nc_2270 goc_nc_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
