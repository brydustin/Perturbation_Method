theory GDCX_nc_021
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0336: "gdc_sub None 336"
  by (gdc_eval gdc_nc_0336)

lemma gdc_nc_0337: "gdc_sub None 337"
  by (gdc_eval gdc_nc_0337)

lemma gdc_nc_0338: "gdc_sub None 338"
  by (gdc_eval gdc_nc_0338)

lemma gdc_nc_0339: "gdc_sub None 339"
  by (gdc_eval gdc_nc_0339)

lemma gdc_nc_0340: "gdc_sub None 340"
  by (gdc_eval gdc_nc_0340)

lemma gdc_nc_0341: "gdc_sub None 341"
  by (gdc_eval gdc_nc_0341)

lemma gdc_nc_0342: "gdc_sub None 342"
  by (gdc_eval gdc_nc_0342)

lemma gdc_nc_0343: "gdc_sub None 343"
  by (gdc_eval gdc_nc_0343)

lemma gdc_nc_0344: "gdc_sub None 344"
  by (gdc_eval gdc_nc_0344)

lemma gdc_nc_0345: "gdc_sub None 345"
  by (gdc_eval gdc_nc_0345)

lemma gdc_nc_0346: "gdc_sub None 346"
  by (gdc_eval gdc_nc_0346)

lemma gdc_nc_0347: "gdc_sub None 347"
  by (gdc_eval gdc_nc_0347)

lemma gdc_nc_0348: "gdc_sub None 348"
  by (gdc_eval gdc_nc_0348)

lemma gdc_nc_0349: "gdc_sub None 349"
  by (gdc_eval gdc_nc_0349)

lemma gdc_nc_0350: "gdc_sub None 350"
  by (gdc_eval gdc_nc_0350)

lemma gdc_nc_0351: "gdc_sub None 351"
  by (gdc_eval gdc_nc_0351)

lemma gupt_nc_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma gsec_nc_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding gupt_nc_021 .
  then show "gdc_sub None j" using gdc_nc_0336 gdc_nc_0337 gdc_nc_0338 gdc_nc_0339 gdc_nc_0340 gdc_nc_0341 gdc_nc_0342 gdc_nc_0343 gdc_nc_0344 gdc_nc_0345 gdc_nc_0346 gdc_nc_0347 gdc_nc_0348 gdc_nc_0349 gdc_nc_0350 gdc_nc_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
