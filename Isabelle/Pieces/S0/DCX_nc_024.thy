theory DCX_nc_024
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0384: "dc_sub None 384"
  by (dc_eval dc_nc_0384)

lemma dc_nc_0385: "dc_sub None 385"
  by (dc_eval dc_nc_0385)

lemma dc_nc_0386: "dc_sub None 386"
  by (dc_eval dc_nc_0386)

lemma dc_nc_0387: "dc_sub None 387"
  by (dc_eval dc_nc_0387)

lemma dc_nc_0388: "dc_sub None 388"
  by (dc_eval dc_nc_0388)

lemma dc_nc_0389: "dc_sub None 389"
  by (dc_eval dc_nc_0389)

lemma dc_nc_0390: "dc_sub None 390"
  by (dc_eval dc_nc_0390)

lemma dc_nc_0391: "dc_sub None 391"
  by (dc_eval dc_nc_0391)

lemma dc_nc_0392: "dc_sub None 392"
  by (dc_eval dc_nc_0392)

lemma dc_nc_0393: "dc_sub None 393"
  by (dc_eval dc_nc_0393)

lemma dc_nc_0394: "dc_sub None 394"
  by (dc_eval dc_nc_0394)

lemma dc_nc_0395: "dc_sub None 395"
  by (dc_eval dc_nc_0395)

lemma dc_nc_0396: "dc_sub None 396"
  by (dc_eval dc_nc_0396)

lemma dc_nc_0397: "dc_sub None 397"
  by (dc_eval dc_nc_0397)

lemma dc_nc_0398: "dc_sub None 398"
  by (dc_eval dc_nc_0398)

lemma dc_nc_0399: "dc_sub None 399"
  by (dc_eval dc_nc_0399)

lemma upt_nc_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma sec_nc_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding upt_nc_024 .
  then show "dc_sub None j" using dc_nc_0384 dc_nc_0385 dc_nc_0386 dc_nc_0387 dc_nc_0388 dc_nc_0389 dc_nc_0390 dc_nc_0391 dc_nc_0392 dc_nc_0393 dc_nc_0394 dc_nc_0395 dc_nc_0396 dc_nc_0397 dc_nc_0398 dc_nc_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
