theory DCX_nc_017
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0272: "dc_sub None 272"
  by (dc_eval dc_nc_0272)

lemma dc_nc_0273: "dc_sub None 273"
  by (dc_eval dc_nc_0273)

lemma dc_nc_0274: "dc_sub None 274"
  by (dc_eval dc_nc_0274)

lemma dc_nc_0275: "dc_sub None 275"
  by (dc_eval dc_nc_0275)

lemma dc_nc_0276: "dc_sub None 276"
  by (dc_eval dc_nc_0276)

lemma dc_nc_0277: "dc_sub None 277"
  by (dc_eval dc_nc_0277)

lemma dc_nc_0278: "dc_sub None 278"
  by (dc_eval dc_nc_0278)

lemma dc_nc_0279: "dc_sub None 279"
  by (dc_eval dc_nc_0279)

lemma dc_nc_0280: "dc_sub None 280"
  by (dc_eval dc_nc_0280)

lemma dc_nc_0281: "dc_sub None 281"
  by (dc_eval dc_nc_0281)

lemma dc_nc_0282: "dc_sub None 282"
  by (dc_eval dc_nc_0282)

lemma dc_nc_0283: "dc_sub None 283"
  by (dc_eval dc_nc_0283)

lemma dc_nc_0284: "dc_sub None 284"
  by (dc_eval dc_nc_0284)

lemma dc_nc_0285: "dc_sub None 285"
  by (dc_eval dc_nc_0285)

lemma dc_nc_0286: "dc_sub None 286"
  by (dc_eval dc_nc_0286)

lemma dc_nc_0287: "dc_sub None 287"
  by (dc_eval dc_nc_0287)

lemma upt_nc_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma sec_nc_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding upt_nc_017 .
  then show "dc_sub None j" using dc_nc_0272 dc_nc_0273 dc_nc_0274 dc_nc_0275 dc_nc_0276 dc_nc_0277 dc_nc_0278 dc_nc_0279 dc_nc_0280 dc_nc_0281 dc_nc_0282 dc_nc_0283 dc_nc_0284 dc_nc_0285 dc_nc_0286 dc_nc_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
