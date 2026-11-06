theory GDCX_nc_038
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0608: "gdc_sub None 608"
  by (gdc_eval gdc_nc_0608)

lemma gdc_nc_0609: "gdc_sub None 609"
  by (gdc_eval gdc_nc_0609)

lemma gdc_nc_0610: "gdc_sub None 610"
  by (gdc_eval gdc_nc_0610)

lemma gdc_nc_0611: "gdc_sub None 611"
  by (gdc_eval gdc_nc_0611)

lemma gdc_nc_0612: "gdc_sub None 612"
  by (gdc_eval gdc_nc_0612)

lemma gdc_nc_0613: "gdc_sub None 613"
  by (gdc_eval gdc_nc_0613)

lemma gdc_nc_0614: "gdc_sub None 614"
  by (gdc_eval gdc_nc_0614)

lemma gdc_nc_0615: "gdc_sub None 615"
  by (gdc_eval gdc_nc_0615)

lemma gdc_nc_0616: "gdc_sub None 616"
  by (gdc_eval gdc_nc_0616)

lemma gdc_nc_0617: "gdc_sub None 617"
  by (gdc_eval gdc_nc_0617)

lemma gdc_nc_0618: "gdc_sub None 618"
  by (gdc_eval gdc_nc_0618)

lemma gdc_nc_0619: "gdc_sub None 619"
  by (gdc_eval gdc_nc_0619)

lemma gdc_nc_0620: "gdc_sub None 620"
  by (gdc_eval gdc_nc_0620)

lemma gdc_nc_0621: "gdc_sub None 621"
  by (gdc_eval gdc_nc_0621)

lemma gdc_nc_0622: "gdc_sub None 622"
  by (gdc_eval gdc_nc_0622)

lemma gdc_nc_0623: "gdc_sub None 623"
  by (gdc_eval gdc_nc_0623)

lemma gupt_nc_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma gsec_nc_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding gupt_nc_038 .
  then show "gdc_sub None j" using gdc_nc_0608 gdc_nc_0609 gdc_nc_0610 gdc_nc_0611 gdc_nc_0612 gdc_nc_0613 gdc_nc_0614 gdc_nc_0615 gdc_nc_0616 gdc_nc_0617 gdc_nc_0618 gdc_nc_0619 gdc_nc_0620 gdc_nc_0621 gdc_nc_0622 gdc_nc_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
