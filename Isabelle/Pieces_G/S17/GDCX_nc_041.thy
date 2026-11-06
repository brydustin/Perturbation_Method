theory GDCX_nc_041
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0656: "gdc_sub None 656"
  by (gdc_eval gdc_nc_0656)

lemma gdc_nc_0657: "gdc_sub None 657"
  by (gdc_eval gdc_nc_0657)

lemma gdc_nc_0658: "gdc_sub None 658"
  by (gdc_eval gdc_nc_0658)

lemma gdc_nc_0659: "gdc_sub None 659"
  by (gdc_eval gdc_nc_0659)

lemma gdc_nc_0660: "gdc_sub None 660"
  by (gdc_eval gdc_nc_0660)

lemma gdc_nc_0661: "gdc_sub None 661"
  by (gdc_eval gdc_nc_0661)

lemma gdc_nc_0662: "gdc_sub None 662"
  by (gdc_eval gdc_nc_0662)

lemma gdc_nc_0663: "gdc_sub None 663"
  by (gdc_eval gdc_nc_0663)

lemma gdc_nc_0664: "gdc_sub None 664"
  by (gdc_eval gdc_nc_0664)

lemma gdc_nc_0665: "gdc_sub None 665"
  by (gdc_eval gdc_nc_0665)

lemma gdc_nc_0666: "gdc_sub None 666"
  by (gdc_eval gdc_nc_0666)

lemma gdc_nc_0667: "gdc_sub None 667"
  by (gdc_eval gdc_nc_0667)

lemma gdc_nc_0668: "gdc_sub None 668"
  by (gdc_eval gdc_nc_0668)

lemma gdc_nc_0669: "gdc_sub None 669"
  by (gdc_eval gdc_nc_0669)

lemma gdc_nc_0670: "gdc_sub None 670"
  by (gdc_eval gdc_nc_0670)

lemma gdc_nc_0671: "gdc_sub None 671"
  by (gdc_eval gdc_nc_0671)

lemma gupt_nc_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma gsec_nc_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding gupt_nc_041 .
  then show "gdc_sub None j" using gdc_nc_0656 gdc_nc_0657 gdc_nc_0658 gdc_nc_0659 gdc_nc_0660 gdc_nc_0661 gdc_nc_0662 gdc_nc_0663 gdc_nc_0664 gdc_nc_0665 gdc_nc_0666 gdc_nc_0667 gdc_nc_0668 gdc_nc_0669 gdc_nc_0670 gdc_nc_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
