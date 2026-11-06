theory DCX_c30_021
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0336: "dc_sub dc_b30 336"
  by (dc_eval dc_c30_0336)

lemma dc_c30_0337: "dc_sub dc_b30 337"
  by (dc_eval dc_c30_0337)

lemma dc_c30_0338: "dc_sub dc_b30 338"
  by (dc_eval dc_c30_0338)

lemma dc_c30_0339: "dc_sub dc_b30 339"
  by (dc_eval dc_c30_0339)

lemma dc_c30_0340: "dc_sub dc_b30 340"
  by (dc_eval dc_c30_0340)

lemma dc_c30_0341: "dc_sub dc_b30 341"
  by (dc_eval dc_c30_0341)

lemma dc_c30_0342: "dc_sub dc_b30 342"
  by (dc_eval dc_c30_0342)

lemma dc_c30_0343: "dc_sub dc_b30 343"
  by (dc_eval dc_c30_0343)

lemma dc_c30_0344: "dc_sub dc_b30 344"
  by (dc_eval dc_c30_0344)

lemma dc_c30_0345: "dc_sub dc_b30 345"
  by (dc_eval dc_c30_0345)

lemma dc_c30_0346: "dc_sub dc_b30 346"
  by (dc_eval dc_c30_0346)

lemma dc_c30_0347: "dc_sub dc_b30 347"
  by (dc_eval dc_c30_0347)

lemma dc_c30_0348: "dc_sub dc_b30 348"
  by (dc_eval dc_c30_0348)

lemma dc_c30_0349: "dc_sub dc_b30 349"
  by (dc_eval dc_c30_0349)

lemma dc_c30_0350: "dc_sub dc_b30 350"
  by (dc_eval dc_c30_0350)

lemma dc_c30_0351: "dc_sub dc_b30 351"
  by (dc_eval dc_c30_0351)

lemma upt_c30_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma sec_c30_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding upt_c30_021 .
  then show "dc_sub dc_b30 j" using dc_c30_0336 dc_c30_0337 dc_c30_0338 dc_c30_0339 dc_c30_0340 dc_c30_0341 dc_c30_0342 dc_c30_0343 dc_c30_0344 dc_c30_0345 dc_c30_0346 dc_c30_0347 dc_c30_0348 dc_c30_0349 dc_c30_0350 dc_c30_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
