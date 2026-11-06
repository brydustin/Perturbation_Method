theory OCX_c30_021
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0336: "oc_sub oc_b30 336"
  by (oc_eval oc_c30_0336)

lemma oc_c30_0337: "oc_sub oc_b30 337"
  by (oc_eval oc_c30_0337)

lemma oc_c30_0338: "oc_sub oc_b30 338"
  by (oc_eval oc_c30_0338)

lemma oc_c30_0339: "oc_sub oc_b30 339"
  by (oc_eval oc_c30_0339)

lemma oc_c30_0340: "oc_sub oc_b30 340"
  by (oc_eval oc_c30_0340)

lemma oc_c30_0341: "oc_sub oc_b30 341"
  by (oc_eval oc_c30_0341)

lemma oc_c30_0342: "oc_sub oc_b30 342"
  by (oc_eval oc_c30_0342)

lemma oc_c30_0343: "oc_sub oc_b30 343"
  by (oc_eval oc_c30_0343)

lemma oc_c30_0344: "oc_sub oc_b30 344"
  by (oc_eval oc_c30_0344)

lemma oc_c30_0345: "oc_sub oc_b30 345"
  by (oc_eval oc_c30_0345)

lemma oc_c30_0346: "oc_sub oc_b30 346"
  by (oc_eval oc_c30_0346)

lemma oc_c30_0347: "oc_sub oc_b30 347"
  by (oc_eval oc_c30_0347)

lemma oc_c30_0348: "oc_sub oc_b30 348"
  by (oc_eval oc_c30_0348)

lemma oc_c30_0349: "oc_sub oc_b30 349"
  by (oc_eval oc_c30_0349)

lemma oc_c30_0350: "oc_sub oc_b30 350"
  by (oc_eval oc_c30_0350)

lemma oc_c30_0351: "oc_sub oc_b30 351"
  by (oc_eval oc_c30_0351)

lemma upt_c30_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma sec_c30_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding upt_c30_021 .
  then show "oc_sub oc_b30 j" using oc_c30_0336 oc_c30_0337 oc_c30_0338 oc_c30_0339 oc_c30_0340 oc_c30_0341 oc_c30_0342 oc_c30_0343 oc_c30_0344 oc_c30_0345 oc_c30_0346 oc_c30_0347 oc_c30_0348 oc_c30_0349 oc_c30_0350 oc_c30_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
