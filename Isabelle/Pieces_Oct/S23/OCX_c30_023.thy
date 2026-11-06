theory OCX_c30_023
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0368: "oc_sub oc_b30 368"
  by (oc_eval oc_c30_0368)

lemma oc_c30_0369: "oc_sub oc_b30 369"
  by (oc_eval oc_c30_0369)

lemma oc_c30_0370: "oc_sub oc_b30 370"
  by (oc_eval oc_c30_0370)

lemma oc_c30_0371: "oc_sub oc_b30 371"
  by (oc_eval oc_c30_0371)

lemma oc_c30_0372: "oc_sub oc_b30 372"
  by (oc_eval oc_c30_0372)

lemma oc_c30_0373: "oc_sub oc_b30 373"
  by (oc_eval oc_c30_0373)

lemma oc_c30_0374: "oc_sub oc_b30 374"
  by (oc_eval oc_c30_0374)

lemma oc_c30_0375: "oc_sub oc_b30 375"
  by (oc_eval oc_c30_0375)

lemma oc_c30_0376: "oc_sub oc_b30 376"
  by (oc_eval oc_c30_0376)

lemma oc_c30_0377: "oc_sub oc_b30 377"
  by (oc_eval oc_c30_0377)

lemma oc_c30_0378: "oc_sub oc_b30 378"
  by (oc_eval oc_c30_0378)

lemma oc_c30_0379: "oc_sub oc_b30 379"
  by (oc_eval oc_c30_0379)

lemma oc_c30_0380: "oc_sub oc_b30 380"
  by (oc_eval oc_c30_0380)

lemma oc_c30_0381: "oc_sub oc_b30 381"
  by (oc_eval oc_c30_0381)

lemma oc_c30_0382: "oc_sub oc_b30 382"
  by (oc_eval oc_c30_0382)

lemma oc_c30_0383: "oc_sub oc_b30 383"
  by (oc_eval oc_c30_0383)

lemma upt_c30_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma sec_c30_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding upt_c30_023 .
  then show "oc_sub oc_b30 j" using oc_c30_0368 oc_c30_0369 oc_c30_0370 oc_c30_0371 oc_c30_0372 oc_c30_0373 oc_c30_0374 oc_c30_0375 oc_c30_0376 oc_c30_0377 oc_c30_0378 oc_c30_0379 oc_c30_0380 oc_c30_0381 oc_c30_0382 oc_c30_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
