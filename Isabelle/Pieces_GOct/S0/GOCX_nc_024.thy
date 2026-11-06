theory GOCX_nc_024
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0384: "goc_sub None 384"
  by (goc_eval goc_nc_0384)

lemma goc_nc_0385: "goc_sub None 385"
  by (goc_eval goc_nc_0385)

lemma goc_nc_0386: "goc_sub None 386"
  by (goc_eval goc_nc_0386)

lemma goc_nc_0387: "goc_sub None 387"
  by (goc_eval goc_nc_0387)

lemma goc_nc_0388: "goc_sub None 388"
  by (goc_eval goc_nc_0388)

lemma goc_nc_0389: "goc_sub None 389"
  by (goc_eval goc_nc_0389)

lemma goc_nc_0390: "goc_sub None 390"
  by (goc_eval goc_nc_0390)

lemma goc_nc_0391: "goc_sub None 391"
  by (goc_eval goc_nc_0391)

lemma goc_nc_0392: "goc_sub None 392"
  by (goc_eval goc_nc_0392)

lemma goc_nc_0393: "goc_sub None 393"
  by (goc_eval goc_nc_0393)

lemma goc_nc_0394: "goc_sub None 394"
  by (goc_eval goc_nc_0394)

lemma goc_nc_0395: "goc_sub None 395"
  by (goc_eval goc_nc_0395)

lemma goc_nc_0396: "goc_sub None 396"
  by (goc_eval goc_nc_0396)

lemma goc_nc_0397: "goc_sub None 397"
  by (goc_eval goc_nc_0397)

lemma goc_nc_0398: "goc_sub None 398"
  by (goc_eval goc_nc_0398)

lemma goc_nc_0399: "goc_sub None 399"
  by (goc_eval goc_nc_0399)

lemma gupt_nc_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma gsec_nc_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding gupt_nc_024 .
  then show "goc_sub None j" using goc_nc_0384 goc_nc_0385 goc_nc_0386 goc_nc_0387 goc_nc_0388 goc_nc_0389 goc_nc_0390 goc_nc_0391 goc_nc_0392 goc_nc_0393 goc_nc_0394 goc_nc_0395 goc_nc_0396 goc_nc_0397 goc_nc_0398 goc_nc_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
