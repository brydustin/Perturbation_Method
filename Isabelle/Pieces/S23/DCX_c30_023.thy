theory DCX_c30_023
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0368: "dc_sub dc_b30 368"
  by (dc_eval dc_c30_0368)

lemma dc_c30_0369: "dc_sub dc_b30 369"
  by (dc_eval dc_c30_0369)

lemma dc_c30_0370: "dc_sub dc_b30 370"
  by (dc_eval dc_c30_0370)

lemma dc_c30_0371: "dc_sub dc_b30 371"
  by (dc_eval dc_c30_0371)

lemma dc_c30_0372: "dc_sub dc_b30 372"
  by (dc_eval dc_c30_0372)

lemma dc_c30_0373: "dc_sub dc_b30 373"
  by (dc_eval dc_c30_0373)

lemma dc_c30_0374: "dc_sub dc_b30 374"
  by (dc_eval dc_c30_0374)

lemma dc_c30_0375: "dc_sub dc_b30 375"
  by (dc_eval dc_c30_0375)

lemma dc_c30_0376: "dc_sub dc_b30 376"
  by (dc_eval dc_c30_0376)

lemma dc_c30_0377: "dc_sub dc_b30 377"
  by (dc_eval dc_c30_0377)

lemma dc_c30_0378: "dc_sub dc_b30 378"
  by (dc_eval dc_c30_0378)

lemma dc_c30_0379: "dc_sub dc_b30 379"
  by (dc_eval dc_c30_0379)

lemma dc_c30_0380: "dc_sub dc_b30 380"
  by (dc_eval dc_c30_0380)

lemma dc_c30_0381: "dc_sub dc_b30 381"
  by (dc_eval dc_c30_0381)

lemma dc_c30_0382: "dc_sub dc_b30 382"
  by (dc_eval dc_c30_0382)

lemma dc_c30_0383: "dc_sub dc_b30 383"
  by (dc_eval dc_c30_0383)

lemma upt_c30_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma sec_c30_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding upt_c30_023 .
  then show "dc_sub dc_b30 j" using dc_c30_0368 dc_c30_0369 dc_c30_0370 dc_c30_0371 dc_c30_0372 dc_c30_0373 dc_c30_0374 dc_c30_0375 dc_c30_0376 dc_c30_0377 dc_c30_0378 dc_c30_0379 dc_c30_0380 dc_c30_0381 dc_c30_0382 dc_c30_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
