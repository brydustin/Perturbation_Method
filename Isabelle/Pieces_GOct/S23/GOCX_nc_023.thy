theory GOCX_nc_023
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0368: "goc_sub None 368"
  by (goc_eval goc_nc_0368)

lemma goc_nc_0369: "goc_sub None 369"
  by (goc_eval goc_nc_0369)

lemma goc_nc_0370: "goc_sub None 370"
  by (goc_eval goc_nc_0370)

lemma goc_nc_0371: "goc_sub None 371"
  by (goc_eval goc_nc_0371)

lemma goc_nc_0372: "goc_sub None 372"
  by (goc_eval goc_nc_0372)

lemma goc_nc_0373: "goc_sub None 373"
  by (goc_eval goc_nc_0373)

lemma goc_nc_0374: "goc_sub None 374"
  by (goc_eval goc_nc_0374)

lemma goc_nc_0375: "goc_sub None 375"
  by (goc_eval goc_nc_0375)

lemma goc_nc_0376: "goc_sub None 376"
  by (goc_eval goc_nc_0376)

lemma goc_nc_0377: "goc_sub None 377"
  by (goc_eval goc_nc_0377)

lemma goc_nc_0378: "goc_sub None 378"
  by (goc_eval goc_nc_0378)

lemma goc_nc_0379: "goc_sub None 379"
  by (goc_eval goc_nc_0379)

lemma goc_nc_0380: "goc_sub None 380"
  by (goc_eval goc_nc_0380)

lemma goc_nc_0381: "goc_sub None 381"
  by (goc_eval goc_nc_0381)

lemma goc_nc_0382: "goc_sub None 382"
  by (goc_eval goc_nc_0382)

lemma goc_nc_0383: "goc_sub None 383"
  by (goc_eval goc_nc_0383)

lemma gupt_nc_023: "[368..<384] = [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]"
  by (simp add: upt_rec)

lemma gsec_nc_023: "\<forall>j\<in>{16 * 23..<16 * 23 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 23..<16 * 23 + 16}"
  then have "j \<in> set [368..<384]" unfolding set_upt by simp
  then have "j \<in> set [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]" unfolding gupt_nc_023 .
  then show "goc_sub None j" using goc_nc_0368 goc_nc_0369 goc_nc_0370 goc_nc_0371 goc_nc_0372 goc_nc_0373 goc_nc_0374 goc_nc_0375 goc_nc_0376 goc_nc_0377 goc_nc_0378 goc_nc_0379 goc_nc_0380 goc_nc_0381 goc_nc_0382 goc_nc_0383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
