theory GDCX_nc_023
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0368: "gdc_sub None 368"
  by (gdc_eval gdc_nc_0368)

lemma gdc_nc_0369: "gdc_sub None 369"
  by (gdc_eval gdc_nc_0369)

lemma gdc_nc_0370: "gdc_sub None 370"
  by (gdc_eval gdc_nc_0370)

lemma gdc_nc_0371: "gdc_sub None 371"
  by (gdc_eval gdc_nc_0371)

lemma gdc_nc_0372: "gdc_sub None 372"
  by (gdc_eval gdc_nc_0372)

lemma gdc_nc_0373: "gdc_sub None 373"
  by (gdc_eval gdc_nc_0373)

lemma gdc_nc_0374: "gdc_sub None 374"
  by (gdc_eval gdc_nc_0374)

lemma gdc_nc_0375: "gdc_sub None 375"
  by (gdc_eval gdc_nc_0375)

lemma gdc_nc_0376: "gdc_sub None 376"
  by (gdc_eval gdc_nc_0376)

lemma gdc_nc_0377: "gdc_sub None 377"
  by (gdc_eval gdc_nc_0377)

lemma gdc_nc_0378: "gdc_sub None 378"
  by (gdc_eval gdc_nc_0378)

lemma gdc_nc_0379: "gdc_sub None 379"
  by (gdc_eval gdc_nc_0379)

lemma gdc_nc_0380: "gdc_sub None 380"
  by (gdc_eval gdc_nc_0380)

lemma gdc_nc_0381: "gdc_sub None 381"
  by (gdc_eval gdc_nc_0381)

lemma gdc_nc_0382: "gdc_sub None 382"
  by (gdc_eval gdc_nc_0382)

lemma gdc_nc_0383: "gdc_sub None 383"
  by (gdc_eval gdc_nc_0383)

lemma gupt_nc_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma gsec_nc_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding gupt_nc_023 .
  then show "gdc_sub None j" using gdc_nc_0368 gdc_nc_0369 gdc_nc_0370 gdc_nc_0371 gdc_nc_0372 gdc_nc_0373 gdc_nc_0374 gdc_nc_0375 gdc_nc_0376 gdc_nc_0377 gdc_nc_0378 gdc_nc_0379 gdc_nc_0380 gdc_nc_0381 gdc_nc_0382 gdc_nc_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
