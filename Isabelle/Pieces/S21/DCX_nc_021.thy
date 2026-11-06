theory DCX_nc_021
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0336: "dc_sub None 336"
  by (dc_eval dc_nc_0336)

lemma dc_nc_0337: "dc_sub None 337"
  by (dc_eval dc_nc_0337)

lemma dc_nc_0338: "dc_sub None 338"
  by (dc_eval dc_nc_0338)

lemma dc_nc_0339: "dc_sub None 339"
  by (dc_eval dc_nc_0339)

lemma dc_nc_0340: "dc_sub None 340"
  by (dc_eval dc_nc_0340)

lemma dc_nc_0341: "dc_sub None 341"
  by (dc_eval dc_nc_0341)

lemma dc_nc_0342: "dc_sub None 342"
  by (dc_eval dc_nc_0342)

lemma dc_nc_0343: "dc_sub None 343"
  by (dc_eval dc_nc_0343)

lemma dc_nc_0344: "dc_sub None 344"
  by (dc_eval dc_nc_0344)

lemma dc_nc_0345: "dc_sub None 345"
  by (dc_eval dc_nc_0345)

lemma dc_nc_0346: "dc_sub None 346"
  by (dc_eval dc_nc_0346)

lemma dc_nc_0347: "dc_sub None 347"
  by (dc_eval dc_nc_0347)

lemma dc_nc_0348: "dc_sub None 348"
  by (dc_eval dc_nc_0348)

lemma dc_nc_0349: "dc_sub None 349"
  by (dc_eval dc_nc_0349)

lemma dc_nc_0350: "dc_sub None 350"
  by (dc_eval dc_nc_0350)

lemma dc_nc_0351: "dc_sub None 351"
  by (dc_eval dc_nc_0351)

lemma upt_nc_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma sec_nc_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding upt_nc_021 .
  then show "dc_sub None j" using dc_nc_0336 dc_nc_0337 dc_nc_0338 dc_nc_0339 dc_nc_0340 dc_nc_0341 dc_nc_0342 dc_nc_0343 dc_nc_0344 dc_nc_0345 dc_nc_0346 dc_nc_0347 dc_nc_0348 dc_nc_0349 dc_nc_0350 dc_nc_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
