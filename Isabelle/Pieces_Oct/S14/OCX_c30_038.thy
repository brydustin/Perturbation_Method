theory OCX_c30_038
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0608: "oc_sub oc_b30 608"
  by (oc_eval oc_c30_0608)

lemma oc_c30_0609: "oc_sub oc_b30 609"
  by (oc_eval oc_c30_0609)

lemma oc_c30_0610: "oc_sub oc_b30 610"
  by (oc_eval oc_c30_0610)

lemma oc_c30_0611: "oc_sub oc_b30 611"
  by (oc_eval oc_c30_0611)

lemma oc_c30_0612: "oc_sub oc_b30 612"
  by (oc_eval oc_c30_0612)

lemma oc_c30_0613: "oc_sub oc_b30 613"
  by (oc_eval oc_c30_0613)

lemma oc_c30_0614: "oc_sub oc_b30 614"
  by (oc_eval oc_c30_0614)

lemma oc_c30_0615: "oc_sub oc_b30 615"
  by (oc_eval oc_c30_0615)

lemma oc_c30_0616: "oc_sub oc_b30 616"
  by (oc_eval oc_c30_0616)

lemma oc_c30_0617: "oc_sub oc_b30 617"
  by (oc_eval oc_c30_0617)

lemma oc_c30_0618: "oc_sub oc_b30 618"
  by (oc_eval oc_c30_0618)

lemma oc_c30_0619: "oc_sub oc_b30 619"
  by (oc_eval oc_c30_0619)

lemma oc_c30_0620: "oc_sub oc_b30 620"
  by (oc_eval oc_c30_0620)

lemma oc_c30_0621: "oc_sub oc_b30 621"
  by (oc_eval oc_c30_0621)

lemma oc_c30_0622: "oc_sub oc_b30 622"
  by (oc_eval oc_c30_0622)

lemma oc_c30_0623: "oc_sub oc_b30 623"
  by (oc_eval oc_c30_0623)

lemma upt_c30_038: "[608..<624] = [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]"
  by (simp add: upt_rec)

lemma sec_c30_038: "\<forall>j\<in>{16 * 38..<16 * 38 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 38..<16 * 38 + 16}"
  then have "j \<in> set [608..<624]" unfolding set_upt by simp
  then have "j \<in> set [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]" unfolding upt_c30_038 .
  then show "oc_sub oc_b30 j" using oc_c30_0608 oc_c30_0609 oc_c30_0610 oc_c30_0611 oc_c30_0612 oc_c30_0613 oc_c30_0614 oc_c30_0615 oc_c30_0616 oc_c30_0617 oc_c30_0618 oc_c30_0619 oc_c30_0620 oc_c30_0621 oc_c30_0622 oc_c30_0623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
