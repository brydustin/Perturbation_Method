theory DCX_c30_038
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0608: "dc_sub dc_b30 608"
  by (dc_eval dc_c30_0608)

lemma dc_c30_0609: "dc_sub dc_b30 609"
  by (dc_eval dc_c30_0609)

lemma dc_c30_0610: "dc_sub dc_b30 610"
  by (dc_eval dc_c30_0610)

lemma dc_c30_0611: "dc_sub dc_b30 611"
  by (dc_eval dc_c30_0611)

lemma dc_c30_0612: "dc_sub dc_b30 612"
  by (dc_eval dc_c30_0612)

lemma dc_c30_0613: "dc_sub dc_b30 613"
  by (dc_eval dc_c30_0613)

lemma dc_c30_0614: "dc_sub dc_b30 614"
  by (dc_eval dc_c30_0614)

lemma dc_c30_0615: "dc_sub dc_b30 615"
  by (dc_eval dc_c30_0615)

lemma dc_c30_0616: "dc_sub dc_b30 616"
  by (dc_eval dc_c30_0616)

lemma dc_c30_0617: "dc_sub dc_b30 617"
  by (dc_eval dc_c30_0617)

lemma dc_c30_0618: "dc_sub dc_b30 618"
  by (dc_eval dc_c30_0618)

lemma dc_c30_0619: "dc_sub dc_b30 619"
  by (dc_eval dc_c30_0619)

lemma dc_c30_0620: "dc_sub dc_b30 620"
  by (dc_eval dc_c30_0620)

lemma dc_c30_0621: "dc_sub dc_b30 621"
  by (dc_eval dc_c30_0621)

lemma dc_c30_0622: "dc_sub dc_b30 622"
  by (dc_eval dc_c30_0622)

lemma dc_c30_0623: "dc_sub dc_b30 623"
  by (dc_eval dc_c30_0623)

lemma upt_c30_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma sec_c30_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding upt_c30_038 .
  then show "dc_sub dc_b30 j" using dc_c30_0608 dc_c30_0609 dc_c30_0610 dc_c30_0611 dc_c30_0612 dc_c30_0613 dc_c30_0614 dc_c30_0615 dc_c30_0616 dc_c30_0617 dc_c30_0618 dc_c30_0619 dc_c30_0620 dc_c30_0621 dc_c30_0622 dc_c30_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
