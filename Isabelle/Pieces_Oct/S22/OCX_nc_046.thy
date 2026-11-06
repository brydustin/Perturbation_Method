theory OCX_nc_046
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0736: "oc_sub None 736"
  by (oc_eval oc_nc_0736)

lemma oc_nc_0737: "oc_sub None 737"
  by (oc_eval oc_nc_0737)

lemma oc_nc_0738: "oc_sub None 738"
  by (oc_eval oc_nc_0738)

lemma oc_nc_0739: "oc_sub None 739"
  by (oc_eval oc_nc_0739)

lemma oc_nc_0740: "oc_sub None 740"
  by (oc_eval oc_nc_0740)

lemma oc_nc_0741: "oc_sub None 741"
  by (oc_eval oc_nc_0741)

lemma oc_nc_0742: "oc_sub None 742"
  by (oc_eval oc_nc_0742)

lemma oc_nc_0743: "oc_sub None 743"
  by (oc_eval oc_nc_0743)

lemma oc_nc_0744: "oc_sub None 744"
  by (oc_eval oc_nc_0744)

lemma oc_nc_0745: "oc_sub None 745"
  by (oc_eval oc_nc_0745)

lemma oc_nc_0746: "oc_sub None 746"
  by (oc_eval oc_nc_0746)

lemma oc_nc_0747: "oc_sub None 747"
  by (oc_eval oc_nc_0747)

lemma oc_nc_0748: "oc_sub None 748"
  by (oc_eval oc_nc_0748)

lemma oc_nc_0749: "oc_sub None 749"
  by (oc_eval oc_nc_0749)

lemma oc_nc_0750: "oc_sub None 750"
  by (oc_eval oc_nc_0750)

lemma oc_nc_0751: "oc_sub None 751"
  by (oc_eval oc_nc_0751)

lemma upt_nc_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma sec_nc_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding upt_nc_046 .
  then show "oc_sub None j" using oc_nc_0736 oc_nc_0737 oc_nc_0738 oc_nc_0739 oc_nc_0740 oc_nc_0741 oc_nc_0742 oc_nc_0743 oc_nc_0744 oc_nc_0745 oc_nc_0746 oc_nc_0747 oc_nc_0748 oc_nc_0749 oc_nc_0750 oc_nc_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
