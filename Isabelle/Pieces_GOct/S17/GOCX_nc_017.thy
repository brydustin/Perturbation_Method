theory GOCX_nc_017
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0272: "goc_sub None 272"
  by (goc_eval goc_nc_0272)

lemma goc_nc_0273: "goc_sub None 273"
  by (goc_eval goc_nc_0273)

lemma goc_nc_0274: "goc_sub None 274"
  by (goc_eval goc_nc_0274)

lemma goc_nc_0275: "goc_sub None 275"
  by (goc_eval goc_nc_0275)

lemma goc_nc_0276: "goc_sub None 276"
  by (goc_eval goc_nc_0276)

lemma goc_nc_0277: "goc_sub None 277"
  by (goc_eval goc_nc_0277)

lemma goc_nc_0278: "goc_sub None 278"
  by (goc_eval goc_nc_0278)

lemma goc_nc_0279: "goc_sub None 279"
  by (goc_eval goc_nc_0279)

lemma goc_nc_0280: "goc_sub None 280"
  by (goc_eval goc_nc_0280)

lemma goc_nc_0281: "goc_sub None 281"
  by (goc_eval goc_nc_0281)

lemma goc_nc_0282: "goc_sub None 282"
  by (goc_eval goc_nc_0282)

lemma goc_nc_0283: "goc_sub None 283"
  by (goc_eval goc_nc_0283)

lemma goc_nc_0284: "goc_sub None 284"
  by (goc_eval goc_nc_0284)

lemma goc_nc_0285: "goc_sub None 285"
  by (goc_eval goc_nc_0285)

lemma goc_nc_0286: "goc_sub None 286"
  by (goc_eval goc_nc_0286)

lemma goc_nc_0287: "goc_sub None 287"
  by (goc_eval goc_nc_0287)

lemma gupt_nc_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma gsec_nc_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding gupt_nc_017 .
  then show "goc_sub None j" using goc_nc_0272 goc_nc_0273 goc_nc_0274 goc_nc_0275 goc_nc_0276 goc_nc_0277 goc_nc_0278 goc_nc_0279 goc_nc_0280 goc_nc_0281 goc_nc_0282 goc_nc_0283 goc_nc_0284 goc_nc_0285 goc_nc_0286 goc_nc_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
