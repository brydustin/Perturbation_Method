theory OCX_nc_041
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0656: "oc_sub None 656"
  by (oc_eval oc_nc_0656)

lemma oc_nc_0657: "oc_sub None 657"
  by (oc_eval oc_nc_0657)

lemma oc_nc_0658: "oc_sub None 658"
  by (oc_eval oc_nc_0658)

lemma oc_nc_0659: "oc_sub None 659"
  by (oc_eval oc_nc_0659)

lemma oc_nc_0660: "oc_sub None 660"
  by (oc_eval oc_nc_0660)

lemma oc_nc_0661: "oc_sub None 661"
  by (oc_eval oc_nc_0661)

lemma oc_nc_0662: "oc_sub None 662"
  by (oc_eval oc_nc_0662)

lemma oc_nc_0663: "oc_sub None 663"
  by (oc_eval oc_nc_0663)

lemma oc_nc_0664: "oc_sub None 664"
  by (oc_eval oc_nc_0664)

lemma oc_nc_0665: "oc_sub None 665"
  by (oc_eval oc_nc_0665)

lemma oc_nc_0666: "oc_sub None 666"
  by (oc_eval oc_nc_0666)

lemma oc_nc_0667: "oc_sub None 667"
  by (oc_eval oc_nc_0667)

lemma oc_nc_0668: "oc_sub None 668"
  by (oc_eval oc_nc_0668)

lemma oc_nc_0669: "oc_sub None 669"
  by (oc_eval oc_nc_0669)

lemma oc_nc_0670: "oc_sub None 670"
  by (oc_eval oc_nc_0670)

lemma oc_nc_0671: "oc_sub None 671"
  by (oc_eval oc_nc_0671)

lemma upt_nc_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma sec_nc_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding upt_nc_041 .
  then show "oc_sub None j" using oc_nc_0656 oc_nc_0657 oc_nc_0658 oc_nc_0659 oc_nc_0660 oc_nc_0661 oc_nc_0662 oc_nc_0663 oc_nc_0664 oc_nc_0665 oc_nc_0666 oc_nc_0667 oc_nc_0668 oc_nc_0669 oc_nc_0670 oc_nc_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
