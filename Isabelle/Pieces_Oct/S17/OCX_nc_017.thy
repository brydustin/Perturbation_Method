theory OCX_nc_017
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0272: "oc_sub None 272"
  by (oc_eval oc_nc_0272)

lemma oc_nc_0273: "oc_sub None 273"
  by (oc_eval oc_nc_0273)

lemma oc_nc_0274: "oc_sub None 274"
  by (oc_eval oc_nc_0274)

lemma oc_nc_0275: "oc_sub None 275"
  by (oc_eval oc_nc_0275)

lemma oc_nc_0276: "oc_sub None 276"
  by (oc_eval oc_nc_0276)

lemma oc_nc_0277: "oc_sub None 277"
  by (oc_eval oc_nc_0277)

lemma oc_nc_0278: "oc_sub None 278"
  by (oc_eval oc_nc_0278)

lemma oc_nc_0279: "oc_sub None 279"
  by (oc_eval oc_nc_0279)

lemma oc_nc_0280: "oc_sub None 280"
  by (oc_eval oc_nc_0280)

lemma oc_nc_0281: "oc_sub None 281"
  by (oc_eval oc_nc_0281)

lemma oc_nc_0282: "oc_sub None 282"
  by (oc_eval oc_nc_0282)

lemma oc_nc_0283: "oc_sub None 283"
  by (oc_eval oc_nc_0283)

lemma oc_nc_0284: "oc_sub None 284"
  by (oc_eval oc_nc_0284)

lemma oc_nc_0285: "oc_sub None 285"
  by (oc_eval oc_nc_0285)

lemma oc_nc_0286: "oc_sub None 286"
  by (oc_eval oc_nc_0286)

lemma oc_nc_0287: "oc_sub None 287"
  by (oc_eval oc_nc_0287)

lemma upt_nc_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma sec_nc_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding upt_nc_017 .
  then show "oc_sub None j" using oc_nc_0272 oc_nc_0273 oc_nc_0274 oc_nc_0275 oc_nc_0276 oc_nc_0277 oc_nc_0278 oc_nc_0279 oc_nc_0280 oc_nc_0281 oc_nc_0282 oc_nc_0283 oc_nc_0284 oc_nc_0285 oc_nc_0286 oc_nc_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
