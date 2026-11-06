theory OCX_nc_038
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0608: "oc_sub None 608"
  by (oc_eval oc_nc_0608)

lemma oc_nc_0609: "oc_sub None 609"
  by (oc_eval oc_nc_0609)

lemma oc_nc_0610: "oc_sub None 610"
  by (oc_eval oc_nc_0610)

lemma oc_nc_0611: "oc_sub None 611"
  by (oc_eval oc_nc_0611)

lemma oc_nc_0612: "oc_sub None 612"
  by (oc_eval oc_nc_0612)

lemma oc_nc_0613: "oc_sub None 613"
  by (oc_eval oc_nc_0613)

lemma oc_nc_0614: "oc_sub None 614"
  by (oc_eval oc_nc_0614)

lemma oc_nc_0615: "oc_sub None 615"
  by (oc_eval oc_nc_0615)

lemma oc_nc_0616: "oc_sub None 616"
  by (oc_eval oc_nc_0616)

lemma oc_nc_0617: "oc_sub None 617"
  by (oc_eval oc_nc_0617)

lemma oc_nc_0618: "oc_sub None 618"
  by (oc_eval oc_nc_0618)

lemma oc_nc_0619: "oc_sub None 619"
  by (oc_eval oc_nc_0619)

lemma oc_nc_0620: "oc_sub None 620"
  by (oc_eval oc_nc_0620)

lemma oc_nc_0621: "oc_sub None 621"
  by (oc_eval oc_nc_0621)

lemma oc_nc_0622: "oc_sub None 622"
  by (oc_eval oc_nc_0622)

lemma oc_nc_0623: "oc_sub None 623"
  by (oc_eval oc_nc_0623)

lemma upt_nc_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma sec_nc_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding upt_nc_038 .
  then show "oc_sub None j" using oc_nc_0608 oc_nc_0609 oc_nc_0610 oc_nc_0611 oc_nc_0612 oc_nc_0613 oc_nc_0614 oc_nc_0615 oc_nc_0616 oc_nc_0617 oc_nc_0618 oc_nc_0619 oc_nc_0620 oc_nc_0621 oc_nc_0622 oc_nc_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
