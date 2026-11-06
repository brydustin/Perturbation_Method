theory GDCX_nc_141
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2256: "gdc_sub None 2256"
  by (gdc_eval gdc_nc_2256)

lemma gdc_nc_2257: "gdc_sub None 2257"
  by (gdc_eval gdc_nc_2257)

lemma gdc_nc_2258: "gdc_sub None 2258"
  by (gdc_eval gdc_nc_2258)

lemma gdc_nc_2259: "gdc_sub None 2259"
  by (gdc_eval gdc_nc_2259)

lemma gdc_nc_2260: "gdc_sub None 2260"
  by (gdc_eval gdc_nc_2260)

lemma gdc_nc_2261: "gdc_sub None 2261"
  by (gdc_eval gdc_nc_2261)

lemma gdc_nc_2262: "gdc_sub None 2262"
  by (gdc_eval gdc_nc_2262)

lemma gdc_nc_2263: "gdc_sub None 2263"
  by (gdc_eval gdc_nc_2263)

lemma gdc_nc_2264: "gdc_sub None 2264"
  by (gdc_eval gdc_nc_2264)

lemma gdc_nc_2265: "gdc_sub None 2265"
  by (gdc_eval gdc_nc_2265)

lemma gdc_nc_2266: "gdc_sub None 2266"
  by (gdc_eval gdc_nc_2266)

lemma gdc_nc_2267: "gdc_sub None 2267"
  by (gdc_eval gdc_nc_2267)

lemma gdc_nc_2268: "gdc_sub None 2268"
  by (gdc_eval gdc_nc_2268)

lemma gdc_nc_2269: "gdc_sub None 2269"
  by (gdc_eval gdc_nc_2269)

lemma gdc_nc_2270: "gdc_sub None 2270"
  by (gdc_eval gdc_nc_2270)

lemma gdc_nc_2271: "gdc_sub None 2271"
  by (gdc_eval gdc_nc_2271)

lemma gupt_nc_141: "[2256..<2272] = [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]"
  by (simp add: upt_rec)

lemma gsec_nc_141: "\<forall>j\<in>{16 * 141..<16 * 141 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 141..<16 * 141 + 16}"
  then have "j \<in> set [2256..<2272]" unfolding set_upt by simp
  then have "j \<in> set [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]" unfolding gupt_nc_141 .
  then show "gdc_sub None j" using gdc_nc_2256 gdc_nc_2257 gdc_nc_2258 gdc_nc_2259 gdc_nc_2260 gdc_nc_2261 gdc_nc_2262 gdc_nc_2263 gdc_nc_2264 gdc_nc_2265 gdc_nc_2266 gdc_nc_2267 gdc_nc_2268 gdc_nc_2269 gdc_nc_2270 gdc_nc_2271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
