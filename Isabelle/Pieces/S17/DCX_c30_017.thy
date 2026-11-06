theory DCX_c30_017
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0272: "dc_sub dc_b30 272"
  by (dc_eval dc_c30_0272)

lemma dc_c30_0273: "dc_sub dc_b30 273"
  by (dc_eval dc_c30_0273)

lemma dc_c30_0274: "dc_sub dc_b30 274"
  by (dc_eval dc_c30_0274)

lemma dc_c30_0275: "dc_sub dc_b30 275"
  by (dc_eval dc_c30_0275)

lemma dc_c30_0276: "dc_sub dc_b30 276"
  by (dc_eval dc_c30_0276)

lemma dc_c30_0277: "dc_sub dc_b30 277"
  by (dc_eval dc_c30_0277)

lemma dc_c30_0278: "dc_sub dc_b30 278"
  by (dc_eval dc_c30_0278)

lemma dc_c30_0279: "dc_sub dc_b30 279"
  by (dc_eval dc_c30_0279)

lemma dc_c30_0280: "dc_sub dc_b30 280"
  by (dc_eval dc_c30_0280)

lemma dc_c30_0281: "dc_sub dc_b30 281"
  by (dc_eval dc_c30_0281)

lemma dc_c30_0282: "dc_sub dc_b30 282"
  by (dc_eval dc_c30_0282)

lemma dc_c30_0283: "dc_sub dc_b30 283"
  by (dc_eval dc_c30_0283)

lemma dc_c30_0284: "dc_sub dc_b30 284"
  by (dc_eval dc_c30_0284)

lemma dc_c30_0285: "dc_sub dc_b30 285"
  by (dc_eval dc_c30_0285)

lemma dc_c30_0286: "dc_sub dc_b30 286"
  by (dc_eval dc_c30_0286)

lemma dc_c30_0287: "dc_sub dc_b30 287"
  by (dc_eval dc_c30_0287)

lemma upt_c30_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma sec_c30_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding upt_c30_017 .
  then show "dc_sub dc_b30 j" using dc_c30_0272 dc_c30_0273 dc_c30_0274 dc_c30_0275 dc_c30_0276 dc_c30_0277 dc_c30_0278 dc_c30_0279 dc_c30_0280 dc_c30_0281 dc_c30_0282 dc_c30_0283 dc_c30_0284 dc_c30_0285 dc_c30_0286 dc_c30_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
