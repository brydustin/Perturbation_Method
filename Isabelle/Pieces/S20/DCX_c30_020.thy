theory DCX_c30_020
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0320: "dc_sub dc_b30 320"
  by (dc_eval dc_c30_0320)

lemma dc_c30_0321: "dc_sub dc_b30 321"
  by (dc_eval dc_c30_0321)

lemma dc_c30_0322: "dc_sub dc_b30 322"
  by (dc_eval dc_c30_0322)

lemma dc_c30_0323: "dc_sub dc_b30 323"
  by (dc_eval dc_c30_0323)

lemma dc_c30_0324: "dc_sub dc_b30 324"
  by (dc_eval dc_c30_0324)

lemma dc_c30_0325: "dc_sub dc_b30 325"
  by (dc_eval dc_c30_0325)

lemma dc_c30_0326: "dc_sub dc_b30 326"
  by (dc_eval dc_c30_0326)

lemma dc_c30_0327: "dc_sub dc_b30 327"
  by (dc_eval dc_c30_0327)

lemma dc_c30_0328: "dc_sub dc_b30 328"
  by (dc_eval dc_c30_0328)

lemma dc_c30_0329: "dc_sub dc_b30 329"
  by (dc_eval dc_c30_0329)

lemma dc_c30_0330: "dc_sub dc_b30 330"
  by (dc_eval dc_c30_0330)

lemma dc_c30_0331: "dc_sub dc_b30 331"
  by (dc_eval dc_c30_0331)

lemma dc_c30_0332: "dc_sub dc_b30 332"
  by (dc_eval dc_c30_0332)

lemma dc_c30_0333: "dc_sub dc_b30 333"
  by (dc_eval dc_c30_0333)

lemma dc_c30_0334: "dc_sub dc_b30 334"
  by (dc_eval dc_c30_0334)

lemma dc_c30_0335: "dc_sub dc_b30 335"
  by (dc_eval dc_c30_0335)

lemma upt_c30_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma sec_c30_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding upt_c30_020 .
  then show "dc_sub dc_b30 j" using dc_c30_0320 dc_c30_0321 dc_c30_0322 dc_c30_0323 dc_c30_0324 dc_c30_0325 dc_c30_0326 dc_c30_0327 dc_c30_0328 dc_c30_0329 dc_c30_0330 dc_c30_0331 dc_c30_0332 dc_c30_0333 dc_c30_0334 dc_c30_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
