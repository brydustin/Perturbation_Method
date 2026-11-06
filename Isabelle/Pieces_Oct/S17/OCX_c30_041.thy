theory OCX_c30_041
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0656: "oc_sub oc_b30 656"
  by (oc_eval oc_c30_0656)

lemma oc_c30_0657: "oc_sub oc_b30 657"
  by (oc_eval oc_c30_0657)

lemma oc_c30_0658: "oc_sub oc_b30 658"
  by (oc_eval oc_c30_0658)

lemma oc_c30_0659: "oc_sub oc_b30 659"
  by (oc_eval oc_c30_0659)

lemma oc_c30_0660: "oc_sub oc_b30 660"
  by (oc_eval oc_c30_0660)

lemma oc_c30_0661: "oc_sub oc_b30 661"
  by (oc_eval oc_c30_0661)

lemma oc_c30_0662: "oc_sub oc_b30 662"
  by (oc_eval oc_c30_0662)

lemma oc_c30_0663: "oc_sub oc_b30 663"
  by (oc_eval oc_c30_0663)

lemma oc_c30_0664: "oc_sub oc_b30 664"
  by (oc_eval oc_c30_0664)

lemma oc_c30_0665: "oc_sub oc_b30 665"
  by (oc_eval oc_c30_0665)

lemma oc_c30_0666: "oc_sub oc_b30 666"
  by (oc_eval oc_c30_0666)

lemma oc_c30_0667: "oc_sub oc_b30 667"
  by (oc_eval oc_c30_0667)

lemma oc_c30_0668: "oc_sub oc_b30 668"
  by (oc_eval oc_c30_0668)

lemma oc_c30_0669: "oc_sub oc_b30 669"
  by (oc_eval oc_c30_0669)

lemma oc_c30_0670: "oc_sub oc_b30 670"
  by (oc_eval oc_c30_0670)

lemma oc_c30_0671: "oc_sub oc_b30 671"
  by (oc_eval oc_c30_0671)

lemma upt_c30_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma sec_c30_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding upt_c30_041 .
  then show "oc_sub oc_b30 j" using oc_c30_0656 oc_c30_0657 oc_c30_0658 oc_c30_0659 oc_c30_0660 oc_c30_0661 oc_c30_0662 oc_c30_0663 oc_c30_0664 oc_c30_0665 oc_c30_0666 oc_c30_0667 oc_c30_0668 oc_c30_0669 oc_c30_0670 oc_c30_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
