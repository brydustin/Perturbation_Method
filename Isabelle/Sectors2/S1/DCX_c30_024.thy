theory DCX_c30_024
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0384: "dc_sub dc_b30 384"
  by (dc_eval dc_c30_0384)

lemma dc_c30_0385: "dc_sub dc_b30 385"
  by (dc_eval dc_c30_0385)

lemma dc_c30_0386: "dc_sub dc_b30 386"
  by (dc_eval dc_c30_0386)

lemma dc_c30_0387: "dc_sub dc_b30 387"
  by (dc_eval dc_c30_0387)

lemma dc_c30_0388: "dc_sub dc_b30 388"
  by (dc_eval dc_c30_0388)

lemma dc_c30_0389: "dc_sub dc_b30 389"
  by (dc_eval dc_c30_0389)

lemma dc_c30_0390: "dc_sub dc_b30 390"
  by (dc_eval dc_c30_0390)

lemma dc_c30_0391: "dc_sub dc_b30 391"
  by (dc_eval dc_c30_0391)

lemma dc_c30_0392: "dc_sub dc_b30 392"
  by (dc_eval dc_c30_0392)

lemma dc_c30_0393: "dc_sub dc_b30 393"
  by (dc_eval dc_c30_0393)

lemma dc_c30_0394: "dc_sub dc_b30 394"
  by (dc_eval dc_c30_0394)

lemma dc_c30_0395: "dc_sub dc_b30 395"
  by (dc_eval dc_c30_0395)

lemma dc_c30_0396: "dc_sub dc_b30 396"
  by (dc_eval dc_c30_0396)

lemma dc_c30_0397: "dc_sub dc_b30 397"
  by (dc_eval dc_c30_0397)

lemma dc_c30_0398: "dc_sub dc_b30 398"
  by (dc_eval dc_c30_0398)

lemma dc_c30_0399: "dc_sub dc_b30 399"
  by (dc_eval dc_c30_0399)

lemma upt_c30_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma sec_c30_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding upt_c30_024 .
  then show "dc_sub dc_b30 j" using dc_c30_0384 dc_c30_0385 dc_c30_0386 dc_c30_0387 dc_c30_0388 dc_c30_0389 dc_c30_0390 dc_c30_0391 dc_c30_0392 dc_c30_0393 dc_c30_0394 dc_c30_0395 dc_c30_0396 dc_c30_0397 dc_c30_0398 dc_c30_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
