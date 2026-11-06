theory DCX_nc_041
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0656: "dc_sub None 656"
  by (dc_eval dc_nc_0656)

lemma dc_nc_0657: "dc_sub None 657"
  by (dc_eval dc_nc_0657)

lemma dc_nc_0658: "dc_sub None 658"
  by (dc_eval dc_nc_0658)

lemma dc_nc_0659: "dc_sub None 659"
  by (dc_eval dc_nc_0659)

lemma dc_nc_0660: "dc_sub None 660"
  by (dc_eval dc_nc_0660)

lemma dc_nc_0661: "dc_sub None 661"
  by (dc_eval dc_nc_0661)

lemma dc_nc_0662: "dc_sub None 662"
  by (dc_eval dc_nc_0662)

lemma dc_nc_0663: "dc_sub None 663"
  by (dc_eval dc_nc_0663)

lemma dc_nc_0664: "dc_sub None 664"
  by (dc_eval dc_nc_0664)

lemma dc_nc_0665: "dc_sub None 665"
  by (dc_eval dc_nc_0665)

lemma dc_nc_0666: "dc_sub None 666"
  by (dc_eval dc_nc_0666)

lemma dc_nc_0667: "dc_sub None 667"
  by (dc_eval dc_nc_0667)

lemma dc_nc_0668: "dc_sub None 668"
  by (dc_eval dc_nc_0668)

lemma dc_nc_0669: "dc_sub None 669"
  by (dc_eval dc_nc_0669)

lemma dc_nc_0670: "dc_sub None 670"
  by (dc_eval dc_nc_0670)

lemma dc_nc_0671: "dc_sub None 671"
  by (dc_eval dc_nc_0671)

lemma upt_nc_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma sec_nc_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding upt_nc_041 .
  then show "dc_sub None j" using dc_nc_0656 dc_nc_0657 dc_nc_0658 dc_nc_0659 dc_nc_0660 dc_nc_0661 dc_nc_0662 dc_nc_0663 dc_nc_0664 dc_nc_0665 dc_nc_0666 dc_nc_0667 dc_nc_0668 dc_nc_0669 dc_nc_0670 dc_nc_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
