theory DCX_nc_020
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0320: "dc_sub None 320"
  by (dc_eval dc_nc_0320)

lemma dc_nc_0321: "dc_sub None 321"
  by (dc_eval dc_nc_0321)

lemma dc_nc_0322: "dc_sub None 322"
  by (dc_eval dc_nc_0322)

lemma dc_nc_0323: "dc_sub None 323"
  by (dc_eval dc_nc_0323)

lemma dc_nc_0324: "dc_sub None 324"
  by (dc_eval dc_nc_0324)

lemma dc_nc_0325: "dc_sub None 325"
  by (dc_eval dc_nc_0325)

lemma dc_nc_0326: "dc_sub None 326"
  by (dc_eval dc_nc_0326)

lemma dc_nc_0327: "dc_sub None 327"
  by (dc_eval dc_nc_0327)

lemma dc_nc_0328: "dc_sub None 328"
  by (dc_eval dc_nc_0328)

lemma dc_nc_0329: "dc_sub None 329"
  by (dc_eval dc_nc_0329)

lemma dc_nc_0330: "dc_sub None 330"
  by (dc_eval dc_nc_0330)

lemma dc_nc_0331: "dc_sub None 331"
  by (dc_eval dc_nc_0331)

lemma dc_nc_0332: "dc_sub None 332"
  by (dc_eval dc_nc_0332)

lemma dc_nc_0333: "dc_sub None 333"
  by (dc_eval dc_nc_0333)

lemma dc_nc_0334: "dc_sub None 334"
  by (dc_eval dc_nc_0334)

lemma dc_nc_0335: "dc_sub None 335"
  by (dc_eval dc_nc_0335)

lemma upt_nc_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma sec_nc_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding upt_nc_020 .
  then show "dc_sub None j" using dc_nc_0320 dc_nc_0321 dc_nc_0322 dc_nc_0323 dc_nc_0324 dc_nc_0325 dc_nc_0326 dc_nc_0327 dc_nc_0328 dc_nc_0329 dc_nc_0330 dc_nc_0331 dc_nc_0332 dc_nc_0333 dc_nc_0334 dc_nc_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
