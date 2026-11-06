theory GOCX_nc_020
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0320: "goc_sub None 320"
  by (goc_eval goc_nc_0320)

lemma goc_nc_0321: "goc_sub None 321"
  by (goc_eval goc_nc_0321)

lemma goc_nc_0322: "goc_sub None 322"
  by (goc_eval goc_nc_0322)

lemma goc_nc_0323: "goc_sub None 323"
  by (goc_eval goc_nc_0323)

lemma goc_nc_0324: "goc_sub None 324"
  by (goc_eval goc_nc_0324)

lemma goc_nc_0325: "goc_sub None 325"
  by (goc_eval goc_nc_0325)

lemma goc_nc_0326: "goc_sub None 326"
  by (goc_eval goc_nc_0326)

lemma goc_nc_0327: "goc_sub None 327"
  by (goc_eval goc_nc_0327)

lemma goc_nc_0328: "goc_sub None 328"
  by (goc_eval goc_nc_0328)

lemma goc_nc_0329: "goc_sub None 329"
  by (goc_eval goc_nc_0329)

lemma goc_nc_0330: "goc_sub None 330"
  by (goc_eval goc_nc_0330)

lemma goc_nc_0331: "goc_sub None 331"
  by (goc_eval goc_nc_0331)

lemma goc_nc_0332: "goc_sub None 332"
  by (goc_eval goc_nc_0332)

lemma goc_nc_0333: "goc_sub None 333"
  by (goc_eval goc_nc_0333)

lemma goc_nc_0334: "goc_sub None 334"
  by (goc_eval goc_nc_0334)

lemma goc_nc_0335: "goc_sub None 335"
  by (goc_eval goc_nc_0335)

lemma gupt_nc_020: "[320..<336] = [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]"
  by (simp add: upt_rec)

lemma gsec_nc_020: "\<forall>j\<in>{16 * 20..<16 * 20 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 20..<16 * 20 + 16}"
  then have "j \<in> set [320..<336]" unfolding set_upt by simp
  then have "j \<in> set [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]" unfolding gupt_nc_020 .
  then show "goc_sub None j" using goc_nc_0320 goc_nc_0321 goc_nc_0322 goc_nc_0323 goc_nc_0324 goc_nc_0325 goc_nc_0326 goc_nc_0327 goc_nc_0328 goc_nc_0329 goc_nc_0330 goc_nc_0331 goc_nc_0332 goc_nc_0333 goc_nc_0334 goc_nc_0335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
