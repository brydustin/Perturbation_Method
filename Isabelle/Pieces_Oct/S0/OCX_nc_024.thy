theory OCX_nc_024
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0384: "oc_sub None 384"
  by (oc_eval oc_nc_0384)

lemma oc_nc_0385: "oc_sub None 385"
  by (oc_eval oc_nc_0385)

lemma oc_nc_0386: "oc_sub None 386"
  by (oc_eval oc_nc_0386)

lemma oc_nc_0387: "oc_sub None 387"
  by (oc_eval oc_nc_0387)

lemma oc_nc_0388: "oc_sub None 388"
  by (oc_eval oc_nc_0388)

lemma oc_nc_0389: "oc_sub None 389"
  by (oc_eval oc_nc_0389)

lemma oc_nc_0390: "oc_sub None 390"
  by (oc_eval oc_nc_0390)

lemma oc_nc_0391: "oc_sub None 391"
  by (oc_eval oc_nc_0391)

lemma oc_nc_0392: "oc_sub None 392"
  by (oc_eval oc_nc_0392)

lemma oc_nc_0393: "oc_sub None 393"
  by (oc_eval oc_nc_0393)

lemma oc_nc_0394: "oc_sub None 394"
  by (oc_eval oc_nc_0394)

lemma oc_nc_0395: "oc_sub None 395"
  by (oc_eval oc_nc_0395)

lemma oc_nc_0396: "oc_sub None 396"
  by (oc_eval oc_nc_0396)

lemma oc_nc_0397: "oc_sub None 397"
  by (oc_eval oc_nc_0397)

lemma oc_nc_0398: "oc_sub None 398"
  by (oc_eval oc_nc_0398)

lemma oc_nc_0399: "oc_sub None 399"
  by (oc_eval oc_nc_0399)

lemma upt_nc_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma sec_nc_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding upt_nc_024 .
  then show "oc_sub None j" using oc_nc_0384 oc_nc_0385 oc_nc_0386 oc_nc_0387 oc_nc_0388 oc_nc_0389 oc_nc_0390 oc_nc_0391 oc_nc_0392 oc_nc_0393 oc_nc_0394 oc_nc_0395 oc_nc_0396 oc_nc_0397 oc_nc_0398 oc_nc_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
