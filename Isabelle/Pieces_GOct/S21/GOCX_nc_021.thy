theory GOCX_nc_021
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0336: "goc_sub None 336"
  by (goc_eval goc_nc_0336)

lemma goc_nc_0337: "goc_sub None 337"
  by (goc_eval goc_nc_0337)

lemma goc_nc_0338: "goc_sub None 338"
  by (goc_eval goc_nc_0338)

lemma goc_nc_0339: "goc_sub None 339"
  by (goc_eval goc_nc_0339)

lemma goc_nc_0340: "goc_sub None 340"
  by (goc_eval goc_nc_0340)

lemma goc_nc_0341: "goc_sub None 341"
  by (goc_eval goc_nc_0341)

lemma goc_nc_0342: "goc_sub None 342"
  by (goc_eval goc_nc_0342)

lemma goc_nc_0343: "goc_sub None 343"
  by (goc_eval goc_nc_0343)

lemma goc_nc_0344: "goc_sub None 344"
  by (goc_eval goc_nc_0344)

lemma goc_nc_0345: "goc_sub None 345"
  by (goc_eval goc_nc_0345)

lemma goc_nc_0346: "goc_sub None 346"
  by (goc_eval goc_nc_0346)

lemma goc_nc_0347: "goc_sub None 347"
  by (goc_eval goc_nc_0347)

lemma goc_nc_0348: "goc_sub None 348"
  by (goc_eval goc_nc_0348)

lemma goc_nc_0349: "goc_sub None 349"
  by (goc_eval goc_nc_0349)

lemma goc_nc_0350: "goc_sub None 350"
  by (goc_eval goc_nc_0350)

lemma goc_nc_0351: "goc_sub None 351"
  by (goc_eval goc_nc_0351)

lemma gupt_nc_021: "[336..<352] = [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]"
  by (simp add: upt_rec)

lemma gsec_nc_021: "\<forall>j\<in>{16 * 21..<16 * 21 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 21..<16 * 21 + 16}"
  then have "j \<in> set [336..<352]" unfolding set_upt by simp
  then have "j \<in> set [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]" unfolding gupt_nc_021 .
  then show "goc_sub None j" using goc_nc_0336 goc_nc_0337 goc_nc_0338 goc_nc_0339 goc_nc_0340 goc_nc_0341 goc_nc_0342 goc_nc_0343 goc_nc_0344 goc_nc_0345 goc_nc_0346 goc_nc_0347 goc_nc_0348 goc_nc_0349 goc_nc_0350 goc_nc_0351
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
