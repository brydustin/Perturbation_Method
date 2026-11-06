theory GDCX_nc_020
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0320: "gdc_sub None 320"
  by (gdc_eval gdc_nc_0320)

lemma gdc_nc_0321: "gdc_sub None 321"
  by (gdc_eval gdc_nc_0321)

lemma gdc_nc_0322: "gdc_sub None 322"
  by (gdc_eval gdc_nc_0322)

lemma gdc_nc_0323: "gdc_sub None 323"
  by (gdc_eval gdc_nc_0323)

lemma gdc_nc_0324: "gdc_sub None 324"
  by (gdc_eval gdc_nc_0324)

lemma gdc_nc_0325: "gdc_sub None 325"
  by (gdc_eval gdc_nc_0325)

lemma gdc_nc_0326: "gdc_sub None 326"
  by (gdc_eval gdc_nc_0326)

lemma gdc_nc_0327: "gdc_sub None 327"
  by (gdc_eval gdc_nc_0327)

lemma gdc_nc_0328: "gdc_sub None 328"
  by (gdc_eval gdc_nc_0328)

lemma gdc_nc_0329: "gdc_sub None 329"
  by (gdc_eval gdc_nc_0329)

lemma gdc_nc_0330: "gdc_sub None 330"
  by (gdc_eval gdc_nc_0330)

lemma gdc_nc_0331: "gdc_sub None 331"
  by (gdc_eval gdc_nc_0331)

lemma gdc_nc_0332: "gdc_sub None 332"
  by (gdc_eval gdc_nc_0332)

lemma gdc_nc_0333: "gdc_sub None 333"
  by (gdc_eval gdc_nc_0333)

lemma gdc_nc_0334: "gdc_sub None 334"
  by (gdc_eval gdc_nc_0334)

lemma gdc_nc_0335: "gdc_sub None 335"
  by (gdc_eval gdc_nc_0335)

lemma gupt_nc_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma gsec_nc_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding gupt_nc_020 .
  then show "gdc_sub None j" using gdc_nc_0320 gdc_nc_0321 gdc_nc_0322 gdc_nc_0323 gdc_nc_0324 gdc_nc_0325 gdc_nc_0326 gdc_nc_0327 gdc_nc_0328 gdc_nc_0329 gdc_nc_0330 gdc_nc_0331 gdc_nc_0332 gdc_nc_0333 gdc_nc_0334 gdc_nc_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
