theory GDCX_nc_017
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0272: "gdc_sub None 272"
  by (gdc_eval gdc_nc_0272)

lemma gdc_nc_0273: "gdc_sub None 273"
  by (gdc_eval gdc_nc_0273)

lemma gdc_nc_0274: "gdc_sub None 274"
  by (gdc_eval gdc_nc_0274)

lemma gdc_nc_0275: "gdc_sub None 275"
  by (gdc_eval gdc_nc_0275)

lemma gdc_nc_0276: "gdc_sub None 276"
  by (gdc_eval gdc_nc_0276)

lemma gdc_nc_0277: "gdc_sub None 277"
  by (gdc_eval gdc_nc_0277)

lemma gdc_nc_0278: "gdc_sub None 278"
  by (gdc_eval gdc_nc_0278)

lemma gdc_nc_0279: "gdc_sub None 279"
  by (gdc_eval gdc_nc_0279)

lemma gdc_nc_0280: "gdc_sub None 280"
  by (gdc_eval gdc_nc_0280)

lemma gdc_nc_0281: "gdc_sub None 281"
  by (gdc_eval gdc_nc_0281)

lemma gdc_nc_0282: "gdc_sub None 282"
  by (gdc_eval gdc_nc_0282)

lemma gdc_nc_0283: "gdc_sub None 283"
  by (gdc_eval gdc_nc_0283)

lemma gdc_nc_0284: "gdc_sub None 284"
  by (gdc_eval gdc_nc_0284)

lemma gdc_nc_0285: "gdc_sub None 285"
  by (gdc_eval gdc_nc_0285)

lemma gdc_nc_0286: "gdc_sub None 286"
  by (gdc_eval gdc_nc_0286)

lemma gdc_nc_0287: "gdc_sub None 287"
  by (gdc_eval gdc_nc_0287)

lemma gupt_nc_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma gsec_nc_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding gupt_nc_017 .
  then show "gdc_sub None j" using gdc_nc_0272 gdc_nc_0273 gdc_nc_0274 gdc_nc_0275 gdc_nc_0276 gdc_nc_0277 gdc_nc_0278 gdc_nc_0279 gdc_nc_0280 gdc_nc_0281 gdc_nc_0282 gdc_nc_0283 gdc_nc_0284 gdc_nc_0285 gdc_nc_0286 gdc_nc_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
