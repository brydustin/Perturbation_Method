theory OCX_c30_020
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0320: "oc_sub oc_b30 320"
  by (oc_eval oc_c30_0320)

lemma oc_c30_0321: "oc_sub oc_b30 321"
  by (oc_eval oc_c30_0321)

lemma oc_c30_0322: "oc_sub oc_b30 322"
  by (oc_eval oc_c30_0322)

lemma oc_c30_0323: "oc_sub oc_b30 323"
  by (oc_eval oc_c30_0323)

lemma oc_c30_0324: "oc_sub oc_b30 324"
  by (oc_eval oc_c30_0324)

lemma oc_c30_0325: "oc_sub oc_b30 325"
  by (oc_eval oc_c30_0325)

lemma oc_c30_0326: "oc_sub oc_b30 326"
  by (oc_eval oc_c30_0326)

lemma oc_c30_0327: "oc_sub oc_b30 327"
  by (oc_eval oc_c30_0327)

lemma oc_c30_0328: "oc_sub oc_b30 328"
  by (oc_eval oc_c30_0328)

lemma oc_c30_0329: "oc_sub oc_b30 329"
  by (oc_eval oc_c30_0329)

lemma oc_c30_0330: "oc_sub oc_b30 330"
  by (oc_eval oc_c30_0330)

lemma oc_c30_0331: "oc_sub oc_b30 331"
  by (oc_eval oc_c30_0331)

lemma oc_c30_0332: "oc_sub oc_b30 332"
  by (oc_eval oc_c30_0332)

lemma oc_c30_0333: "oc_sub oc_b30 333"
  by (oc_eval oc_c30_0333)

lemma oc_c30_0334: "oc_sub oc_b30 334"
  by (oc_eval oc_c30_0334)

lemma oc_c30_0335: "oc_sub oc_b30 335"
  by (oc_eval oc_c30_0335)

lemma upt_c30_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma sec_c30_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding upt_c30_020 .
  then show "oc_sub oc_b30 j" using oc_c30_0320 oc_c30_0321 oc_c30_0322 oc_c30_0323 oc_c30_0324 oc_c30_0325 oc_c30_0326 oc_c30_0327 oc_c30_0328 oc_c30_0329 oc_c30_0330 oc_c30_0331 oc_c30_0332 oc_c30_0333 oc_c30_0334 oc_c30_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
