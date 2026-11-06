theory OCX_nc_021
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0336: "oc_sub None 336"
  by (oc_eval oc_nc_0336)

lemma oc_nc_0337: "oc_sub None 337"
  by (oc_eval oc_nc_0337)

lemma oc_nc_0338: "oc_sub None 338"
  by (oc_eval oc_nc_0338)

lemma oc_nc_0339: "oc_sub None 339"
  by (oc_eval oc_nc_0339)

lemma oc_nc_0340: "oc_sub None 340"
  by (oc_eval oc_nc_0340)

lemma oc_nc_0341: "oc_sub None 341"
  by (oc_eval oc_nc_0341)

lemma oc_nc_0342: "oc_sub None 342"
  by (oc_eval oc_nc_0342)

lemma oc_nc_0343: "oc_sub None 343"
  by (oc_eval oc_nc_0343)

lemma oc_nc_0344: "oc_sub None 344"
  by (oc_eval oc_nc_0344)

lemma oc_nc_0345: "oc_sub None 345"
  by (oc_eval oc_nc_0345)

lemma oc_nc_0346: "oc_sub None 346"
  by (oc_eval oc_nc_0346)

lemma oc_nc_0347: "oc_sub None 347"
  by (oc_eval oc_nc_0347)

lemma oc_nc_0348: "oc_sub None 348"
  by (oc_eval oc_nc_0348)

lemma oc_nc_0349: "oc_sub None 349"
  by (oc_eval oc_nc_0349)

lemma oc_nc_0350: "oc_sub None 350"
  by (oc_eval oc_nc_0350)

lemma oc_nc_0351: "oc_sub None 351"
  by (oc_eval oc_nc_0351)

lemma upt_nc_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma sec_nc_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding upt_nc_021 .
  then show "oc_sub None j" using oc_nc_0336 oc_nc_0337 oc_nc_0338 oc_nc_0339 oc_nc_0340 oc_nc_0341 oc_nc_0342 oc_nc_0343 oc_nc_0344 oc_nc_0345 oc_nc_0346 oc_nc_0347 oc_nc_0348 oc_nc_0349 oc_nc_0350 oc_nc_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
