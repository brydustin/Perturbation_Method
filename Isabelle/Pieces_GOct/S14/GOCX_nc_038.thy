theory GOCX_nc_038
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0608: "goc_sub None 608"
  by (goc_eval goc_nc_0608)

lemma goc_nc_0609: "goc_sub None 609"
  by (goc_eval goc_nc_0609)

lemma goc_nc_0610: "goc_sub None 610"
  by (goc_eval goc_nc_0610)

lemma goc_nc_0611: "goc_sub None 611"
  by (goc_eval goc_nc_0611)

lemma goc_nc_0612: "goc_sub None 612"
  by (goc_eval goc_nc_0612)

lemma goc_nc_0613: "goc_sub None 613"
  by (goc_eval goc_nc_0613)

lemma goc_nc_0614: "goc_sub None 614"
  by (goc_eval goc_nc_0614)

lemma goc_nc_0615: "goc_sub None 615"
  by (goc_eval goc_nc_0615)

lemma goc_nc_0616: "goc_sub None 616"
  by (goc_eval goc_nc_0616)

lemma goc_nc_0617: "goc_sub None 617"
  by (goc_eval goc_nc_0617)

lemma goc_nc_0618: "goc_sub None 618"
  by (goc_eval goc_nc_0618)

lemma goc_nc_0619: "goc_sub None 619"
  by (goc_eval goc_nc_0619)

lemma goc_nc_0620: "goc_sub None 620"
  by (goc_eval goc_nc_0620)

lemma goc_nc_0621: "goc_sub None 621"
  by (goc_eval goc_nc_0621)

lemma goc_nc_0622: "goc_sub None 622"
  by (goc_eval goc_nc_0622)

lemma goc_nc_0623: "goc_sub None 623"
  by (goc_eval goc_nc_0623)

lemma gupt_nc_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma gsec_nc_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding gupt_nc_038 .
  then show "goc_sub None j" using goc_nc_0608 goc_nc_0609 goc_nc_0610 goc_nc_0611 goc_nc_0612 goc_nc_0613 goc_nc_0614 goc_nc_0615 goc_nc_0616 goc_nc_0617 goc_nc_0618 goc_nc_0619 goc_nc_0620 goc_nc_0621 goc_nc_0622 goc_nc_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
