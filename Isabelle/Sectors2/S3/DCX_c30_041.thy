theory DCX_c30_041
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0656: "dc_sub dc_b30 656"
  by (dc_eval dc_c30_0656)

lemma dc_c30_0657: "dc_sub dc_b30 657"
  by (dc_eval dc_c30_0657)

lemma dc_c30_0658: "dc_sub dc_b30 658"
  by (dc_eval dc_c30_0658)

lemma dc_c30_0659: "dc_sub dc_b30 659"
  by (dc_eval dc_c30_0659)

lemma dc_c30_0660: "dc_sub dc_b30 660"
  by (dc_eval dc_c30_0660)

lemma dc_c30_0661: "dc_sub dc_b30 661"
  by (dc_eval dc_c30_0661)

lemma dc_c30_0662: "dc_sub dc_b30 662"
  by (dc_eval dc_c30_0662)

lemma dc_c30_0663: "dc_sub dc_b30 663"
  by (dc_eval dc_c30_0663)

lemma dc_c30_0664: "dc_sub dc_b30 664"
  by (dc_eval dc_c30_0664)

lemma dc_c30_0665: "dc_sub dc_b30 665"
  by (dc_eval dc_c30_0665)

lemma dc_c30_0666: "dc_sub dc_b30 666"
  by (dc_eval dc_c30_0666)

lemma dc_c30_0667: "dc_sub dc_b30 667"
  by (dc_eval dc_c30_0667)

lemma dc_c30_0668: "dc_sub dc_b30 668"
  by (dc_eval dc_c30_0668)

lemma dc_c30_0669: "dc_sub dc_b30 669"
  by (dc_eval dc_c30_0669)

lemma dc_c30_0670: "dc_sub dc_b30 670"
  by (dc_eval dc_c30_0670)

lemma dc_c30_0671: "dc_sub dc_b30 671"
  by (dc_eval dc_c30_0671)

lemma upt_c30_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma sec_c30_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding upt_c30_041 .
  then show "dc_sub dc_b30 j" using dc_c30_0656 dc_c30_0657 dc_c30_0658 dc_c30_0659 dc_c30_0660 dc_c30_0661 dc_c30_0662 dc_c30_0663 dc_c30_0664 dc_c30_0665 dc_c30_0666 dc_c30_0667 dc_c30_0668 dc_c30_0669 dc_c30_0670 dc_c30_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
