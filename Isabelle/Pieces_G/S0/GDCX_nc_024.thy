theory GDCX_nc_024
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0384: "gdc_sub None 384"
  by (gdc_eval gdc_nc_0384)

lemma gdc_nc_0385: "gdc_sub None 385"
  by (gdc_eval gdc_nc_0385)

lemma gdc_nc_0386: "gdc_sub None 386"
  by (gdc_eval gdc_nc_0386)

lemma gdc_nc_0387: "gdc_sub None 387"
  by (gdc_eval gdc_nc_0387)

lemma gdc_nc_0388: "gdc_sub None 388"
  by (gdc_eval gdc_nc_0388)

lemma gdc_nc_0389: "gdc_sub None 389"
  by (gdc_eval gdc_nc_0389)

lemma gdc_nc_0390: "gdc_sub None 390"
  by (gdc_eval gdc_nc_0390)

lemma gdc_nc_0391: "gdc_sub None 391"
  by (gdc_eval gdc_nc_0391)

lemma gdc_nc_0392: "gdc_sub None 392"
  by (gdc_eval gdc_nc_0392)

lemma gdc_nc_0393: "gdc_sub None 393"
  by (gdc_eval gdc_nc_0393)

lemma gdc_nc_0394: "gdc_sub None 394"
  by (gdc_eval gdc_nc_0394)

lemma gdc_nc_0395: "gdc_sub None 395"
  by (gdc_eval gdc_nc_0395)

lemma gdc_nc_0396: "gdc_sub None 396"
  by (gdc_eval gdc_nc_0396)

lemma gdc_nc_0397: "gdc_sub None 397"
  by (gdc_eval gdc_nc_0397)

lemma gdc_nc_0398: "gdc_sub None 398"
  by (gdc_eval gdc_nc_0398)

lemma gdc_nc_0399: "gdc_sub None 399"
  by (gdc_eval gdc_nc_0399)

lemma gupt_nc_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma gsec_nc_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding gupt_nc_024 .
  then show "gdc_sub None j" using gdc_nc_0384 gdc_nc_0385 gdc_nc_0386 gdc_nc_0387 gdc_nc_0388 gdc_nc_0389 gdc_nc_0390 gdc_nc_0391 gdc_nc_0392 gdc_nc_0393 gdc_nc_0394 gdc_nc_0395 gdc_nc_0396 gdc_nc_0397 gdc_nc_0398 gdc_nc_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
