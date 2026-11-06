theory OCX_c30_024
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0384: "oc_sub oc_b30 384"
  by (oc_eval oc_c30_0384)

lemma oc_c30_0385: "oc_sub oc_b30 385"
  by (oc_eval oc_c30_0385)

lemma oc_c30_0386: "oc_sub oc_b30 386"
  by (oc_eval oc_c30_0386)

lemma oc_c30_0387: "oc_sub oc_b30 387"
  by (oc_eval oc_c30_0387)

lemma oc_c30_0388: "oc_sub oc_b30 388"
  by (oc_eval oc_c30_0388)

lemma oc_c30_0389: "oc_sub oc_b30 389"
  by (oc_eval oc_c30_0389)

lemma oc_c30_0390: "oc_sub oc_b30 390"
  by (oc_eval oc_c30_0390)

lemma oc_c30_0391: "oc_sub oc_b30 391"
  by (oc_eval oc_c30_0391)

lemma oc_c30_0392: "oc_sub oc_b30 392"
  by (oc_eval oc_c30_0392)

lemma oc_c30_0393: "oc_sub oc_b30 393"
  by (oc_eval oc_c30_0393)

lemma oc_c30_0394: "oc_sub oc_b30 394"
  by (oc_eval oc_c30_0394)

lemma oc_c30_0395: "oc_sub oc_b30 395"
  by (oc_eval oc_c30_0395)

lemma oc_c30_0396: "oc_sub oc_b30 396"
  by (oc_eval oc_c30_0396)

lemma oc_c30_0397: "oc_sub oc_b30 397"
  by (oc_eval oc_c30_0397)

lemma oc_c30_0398: "oc_sub oc_b30 398"
  by (oc_eval oc_c30_0398)

lemma oc_c30_0399: "oc_sub oc_b30 399"
  by (oc_eval oc_c30_0399)

lemma upt_c30_024: "[384..<400] = [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]"
  by (simp add: upt_rec)

lemma sec_c30_024: "\<forall>j\<in>{16 * 24..<16 * 24 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 24..<16 * 24 + 16}"
  then have "j \<in> set [384..<400]" unfolding set_upt by simp
  then have "j \<in> set [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399]" unfolding upt_c30_024 .
  then show "oc_sub oc_b30 j" using oc_c30_0384 oc_c30_0385 oc_c30_0386 oc_c30_0387 oc_c30_0388 oc_c30_0389 oc_c30_0390 oc_c30_0391 oc_c30_0392 oc_c30_0393 oc_c30_0394 oc_c30_0395 oc_c30_0396 oc_c30_0397 oc_c30_0398 oc_c30_0399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
