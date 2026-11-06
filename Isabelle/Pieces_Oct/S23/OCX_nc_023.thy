theory OCX_nc_023
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0368: "oc_sub None 368"
  by (oc_eval oc_nc_0368)

lemma oc_nc_0369: "oc_sub None 369"
  by (oc_eval oc_nc_0369)

lemma oc_nc_0370: "oc_sub None 370"
  by (oc_eval oc_nc_0370)

lemma oc_nc_0371: "oc_sub None 371"
  by (oc_eval oc_nc_0371)

lemma oc_nc_0372: "oc_sub None 372"
  by (oc_eval oc_nc_0372)

lemma oc_nc_0373: "oc_sub None 373"
  by (oc_eval oc_nc_0373)

lemma oc_nc_0374: "oc_sub None 374"
  by (oc_eval oc_nc_0374)

lemma oc_nc_0375: "oc_sub None 375"
  by (oc_eval oc_nc_0375)

lemma oc_nc_0376: "oc_sub None 376"
  by (oc_eval oc_nc_0376)

lemma oc_nc_0377: "oc_sub None 377"
  by (oc_eval oc_nc_0377)

lemma oc_nc_0378: "oc_sub None 378"
  by (oc_eval oc_nc_0378)

lemma oc_nc_0379: "oc_sub None 379"
  by (oc_eval oc_nc_0379)

lemma oc_nc_0380: "oc_sub None 380"
  by (oc_eval oc_nc_0380)

lemma oc_nc_0381: "oc_sub None 381"
  by (oc_eval oc_nc_0381)

lemma oc_nc_0382: "oc_sub None 382"
  by (oc_eval oc_nc_0382)

lemma oc_nc_0383: "oc_sub None 383"
  by (oc_eval oc_nc_0383)

lemma upt_nc_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma sec_nc_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding upt_nc_023 .
  then show "oc_sub None j" using oc_nc_0368 oc_nc_0369 oc_nc_0370 oc_nc_0371 oc_nc_0372 oc_nc_0373 oc_nc_0374 oc_nc_0375 oc_nc_0376 oc_nc_0377 oc_nc_0378 oc_nc_0379 oc_nc_0380 oc_nc_0381 oc_nc_0382 oc_nc_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
