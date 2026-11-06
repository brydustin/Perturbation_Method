theory DCX_nc_023
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0368: "dc_sub None 368"
  by (dc_eval dc_nc_0368)

lemma dc_nc_0369: "dc_sub None 369"
  by (dc_eval dc_nc_0369)

lemma dc_nc_0370: "dc_sub None 370"
  by (dc_eval dc_nc_0370)

lemma dc_nc_0371: "dc_sub None 371"
  by (dc_eval dc_nc_0371)

lemma dc_nc_0372: "dc_sub None 372"
  by (dc_eval dc_nc_0372)

lemma dc_nc_0373: "dc_sub None 373"
  by (dc_eval dc_nc_0373)

lemma dc_nc_0374: "dc_sub None 374"
  by (dc_eval dc_nc_0374)

lemma dc_nc_0375: "dc_sub None 375"
  by (dc_eval dc_nc_0375)

lemma dc_nc_0376: "dc_sub None 376"
  by (dc_eval dc_nc_0376)

lemma dc_nc_0377: "dc_sub None 377"
  by (dc_eval dc_nc_0377)

lemma dc_nc_0378: "dc_sub None 378"
  by (dc_eval dc_nc_0378)

lemma dc_nc_0379: "dc_sub None 379"
  by (dc_eval dc_nc_0379)

lemma dc_nc_0380: "dc_sub None 380"
  by (dc_eval dc_nc_0380)

lemma dc_nc_0381: "dc_sub None 381"
  by (dc_eval dc_nc_0381)

lemma dc_nc_0382: "dc_sub None 382"
  by (dc_eval dc_nc_0382)

lemma dc_nc_0383: "dc_sub None 383"
  by (dc_eval dc_nc_0383)

lemma upt_nc_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma sec_nc_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding upt_nc_023 .
  then show "dc_sub None j" using dc_nc_0368 dc_nc_0369 dc_nc_0370 dc_nc_0371 dc_nc_0372 dc_nc_0373 dc_nc_0374 dc_nc_0375 dc_nc_0376 dc_nc_0377 dc_nc_0378 dc_nc_0379 dc_nc_0380 dc_nc_0381 dc_nc_0382 dc_nc_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
