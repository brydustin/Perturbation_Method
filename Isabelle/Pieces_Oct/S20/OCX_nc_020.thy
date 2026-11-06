theory OCX_nc_020
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0320: "oc_sub None 320"
  by (oc_eval oc_nc_0320)

lemma oc_nc_0321: "oc_sub None 321"
  by (oc_eval oc_nc_0321)

lemma oc_nc_0322: "oc_sub None 322"
  by (oc_eval oc_nc_0322)

lemma oc_nc_0323: "oc_sub None 323"
  by (oc_eval oc_nc_0323)

lemma oc_nc_0324: "oc_sub None 324"
  by (oc_eval oc_nc_0324)

lemma oc_nc_0325: "oc_sub None 325"
  by (oc_eval oc_nc_0325)

lemma oc_nc_0326: "oc_sub None 326"
  by (oc_eval oc_nc_0326)

lemma oc_nc_0327: "oc_sub None 327"
  by (oc_eval oc_nc_0327)

lemma oc_nc_0328: "oc_sub None 328"
  by (oc_eval oc_nc_0328)

lemma oc_nc_0329: "oc_sub None 329"
  by (oc_eval oc_nc_0329)

lemma oc_nc_0330: "oc_sub None 330"
  by (oc_eval oc_nc_0330)

lemma oc_nc_0331: "oc_sub None 331"
  by (oc_eval oc_nc_0331)

lemma oc_nc_0332: "oc_sub None 332"
  by (oc_eval oc_nc_0332)

lemma oc_nc_0333: "oc_sub None 333"
  by (oc_eval oc_nc_0333)

lemma oc_nc_0334: "oc_sub None 334"
  by (oc_eval oc_nc_0334)

lemma oc_nc_0335: "oc_sub None 335"
  by (oc_eval oc_nc_0335)

lemma upt_nc_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma sec_nc_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding upt_nc_020 .
  then show "oc_sub None j" using oc_nc_0320 oc_nc_0321 oc_nc_0322 oc_nc_0323 oc_nc_0324 oc_nc_0325 oc_nc_0326 oc_nc_0327 oc_nc_0328 oc_nc_0329 oc_nc_0330 oc_nc_0331 oc_nc_0332 oc_nc_0333 oc_nc_0334 oc_nc_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
