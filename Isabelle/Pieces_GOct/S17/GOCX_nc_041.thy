theory GOCX_nc_041
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0656: "goc_sub None 656"
  by (goc_eval goc_nc_0656)

lemma goc_nc_0657: "goc_sub None 657"
  by (goc_eval goc_nc_0657)

lemma goc_nc_0658: "goc_sub None 658"
  by (goc_eval goc_nc_0658)

lemma goc_nc_0659: "goc_sub None 659"
  by (goc_eval goc_nc_0659)

lemma goc_nc_0660: "goc_sub None 660"
  by (goc_eval goc_nc_0660)

lemma goc_nc_0661: "goc_sub None 661"
  by (goc_eval goc_nc_0661)

lemma goc_nc_0662: "goc_sub None 662"
  by (goc_eval goc_nc_0662)

lemma goc_nc_0663: "goc_sub None 663"
  by (goc_eval goc_nc_0663)

lemma goc_nc_0664: "goc_sub None 664"
  by (goc_eval goc_nc_0664)

lemma goc_nc_0665: "goc_sub None 665"
  by (goc_eval goc_nc_0665)

lemma goc_nc_0666: "goc_sub None 666"
  by (goc_eval goc_nc_0666)

lemma goc_nc_0667: "goc_sub None 667"
  by (goc_eval goc_nc_0667)

lemma goc_nc_0668: "goc_sub None 668"
  by (goc_eval goc_nc_0668)

lemma goc_nc_0669: "goc_sub None 669"
  by (goc_eval goc_nc_0669)

lemma goc_nc_0670: "goc_sub None 670"
  by (goc_eval goc_nc_0670)

lemma goc_nc_0671: "goc_sub None 671"
  by (goc_eval goc_nc_0671)

lemma gupt_nc_041: "[656..<672] = [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]"
  by (simp add: upt_rec)

lemma gsec_nc_041: "\<forall>j\<in>{16 * 41..<16 * 41 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 41..<16 * 41 + 16}"
  then have "j \<in> set [656..<672]" unfolding set_upt by simp
  then have "j \<in> set [656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]" unfolding gupt_nc_041 .
  then show "goc_sub None j" using goc_nc_0656 goc_nc_0657 goc_nc_0658 goc_nc_0659 goc_nc_0660 goc_nc_0661 goc_nc_0662 goc_nc_0663 goc_nc_0664 goc_nc_0665 goc_nc_0666 goc_nc_0667 goc_nc_0668 goc_nc_0669 goc_nc_0670 goc_nc_0671
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
