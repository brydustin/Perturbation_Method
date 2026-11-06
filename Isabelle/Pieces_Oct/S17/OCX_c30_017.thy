theory OCX_c30_017
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0272: "oc_sub oc_b30 272"
  by (oc_eval oc_c30_0272)

lemma oc_c30_0273: "oc_sub oc_b30 273"
  by (oc_eval oc_c30_0273)

lemma oc_c30_0274: "oc_sub oc_b30 274"
  by (oc_eval oc_c30_0274)

lemma oc_c30_0275: "oc_sub oc_b30 275"
  by (oc_eval oc_c30_0275)

lemma oc_c30_0276: "oc_sub oc_b30 276"
  by (oc_eval oc_c30_0276)

lemma oc_c30_0277: "oc_sub oc_b30 277"
  by (oc_eval oc_c30_0277)

lemma oc_c30_0278: "oc_sub oc_b30 278"
  by (oc_eval oc_c30_0278)

lemma oc_c30_0279: "oc_sub oc_b30 279"
  by (oc_eval oc_c30_0279)

lemma oc_c30_0280: "oc_sub oc_b30 280"
  by (oc_eval oc_c30_0280)

lemma oc_c30_0281: "oc_sub oc_b30 281"
  by (oc_eval oc_c30_0281)

lemma oc_c30_0282: "oc_sub oc_b30 282"
  by (oc_eval oc_c30_0282)

lemma oc_c30_0283: "oc_sub oc_b30 283"
  by (oc_eval oc_c30_0283)

lemma oc_c30_0284: "oc_sub oc_b30 284"
  by (oc_eval oc_c30_0284)

lemma oc_c30_0285: "oc_sub oc_b30 285"
  by (oc_eval oc_c30_0285)

lemma oc_c30_0286: "oc_sub oc_b30 286"
  by (oc_eval oc_c30_0286)

lemma oc_c30_0287: "oc_sub oc_b30 287"
  by (oc_eval oc_c30_0287)

lemma upt_c30_017: "[272..<288] = [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]"
  by (simp add: upt_rec)

lemma sec_c30_017: "\<forall>j\<in>{16 * 17..<16 * 17 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 17..<16 * 17 + 16}"
  then have "j \<in> set [272..<288]" unfolding set_upt by simp
  then have "j \<in> set [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]" unfolding upt_c30_017 .
  then show "oc_sub oc_b30 j" using oc_c30_0272 oc_c30_0273 oc_c30_0274 oc_c30_0275 oc_c30_0276 oc_c30_0277 oc_c30_0278 oc_c30_0279 oc_c30_0280 oc_c30_0281 oc_c30_0282 oc_c30_0283 oc_c30_0284 oc_c30_0285 oc_c30_0286 oc_c30_0287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
