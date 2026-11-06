theory DCX_nc_038
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0608: "dc_sub None 608"
  by (dc_eval dc_nc_0608)

lemma dc_nc_0609: "dc_sub None 609"
  by (dc_eval dc_nc_0609)

lemma dc_nc_0610: "dc_sub None 610"
  by (dc_eval dc_nc_0610)

lemma dc_nc_0611: "dc_sub None 611"
  by (dc_eval dc_nc_0611)

lemma dc_nc_0612: "dc_sub None 612"
  by (dc_eval dc_nc_0612)

lemma dc_nc_0613: "dc_sub None 613"
  by (dc_eval dc_nc_0613)

lemma dc_nc_0614: "dc_sub None 614"
  by (dc_eval dc_nc_0614)

lemma dc_nc_0615: "dc_sub None 615"
  by (dc_eval dc_nc_0615)

lemma dc_nc_0616: "dc_sub None 616"
  by (dc_eval dc_nc_0616)

lemma dc_nc_0617: "dc_sub None 617"
  by (dc_eval dc_nc_0617)

lemma dc_nc_0618: "dc_sub None 618"
  by (dc_eval dc_nc_0618)

lemma dc_nc_0619: "dc_sub None 619"
  by (dc_eval dc_nc_0619)

lemma dc_nc_0620: "dc_sub None 620"
  by (dc_eval dc_nc_0620)

lemma dc_nc_0621: "dc_sub None 621"
  by (dc_eval dc_nc_0621)

lemma dc_nc_0622: "dc_sub None 622"
  by (dc_eval dc_nc_0622)

lemma dc_nc_0623: "dc_sub None 623"
  by (dc_eval dc_nc_0623)

lemma upt_nc_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma sec_nc_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding upt_nc_038 .
  then show "dc_sub None j" using dc_nc_0608 dc_nc_0609 dc_nc_0610 dc_nc_0611 dc_nc_0612 dc_nc_0613 dc_nc_0614 dc_nc_0615 dc_nc_0616 dc_nc_0617 dc_nc_0618 dc_nc_0619 dc_nc_0620 dc_nc_0621 dc_nc_0622 dc_nc_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
