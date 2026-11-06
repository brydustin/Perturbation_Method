theory DCX_nc_046
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0736: "dc_sub None 736"
  by (dc_eval dc_nc_0736)

lemma dc_nc_0737: "dc_sub None 737"
  by (dc_eval dc_nc_0737)

lemma dc_nc_0738: "dc_sub None 738"
  by (dc_eval dc_nc_0738)

lemma dc_nc_0739: "dc_sub None 739"
  by (dc_eval dc_nc_0739)

lemma dc_nc_0740: "dc_sub None 740"
  by (dc_eval dc_nc_0740)

lemma dc_nc_0741: "dc_sub None 741"
  by (dc_eval dc_nc_0741)

lemma dc_nc_0742: "dc_sub None 742"
  by (dc_eval dc_nc_0742)

lemma dc_nc_0743: "dc_sub None 743"
  by (dc_eval dc_nc_0743)

lemma dc_nc_0744: "dc_sub None 744"
  by (dc_eval dc_nc_0744)

lemma dc_nc_0745: "dc_sub None 745"
  by (dc_eval dc_nc_0745)

lemma dc_nc_0746: "dc_sub None 746"
  by (dc_eval dc_nc_0746)

lemma dc_nc_0747: "dc_sub None 747"
  by (dc_eval dc_nc_0747)

lemma dc_nc_0748: "dc_sub None 748"
  by (dc_eval dc_nc_0748)

lemma dc_nc_0749: "dc_sub None 749"
  by (dc_eval dc_nc_0749)

lemma dc_nc_0750: "dc_sub None 750"
  by (dc_eval dc_nc_0750)

lemma dc_nc_0751: "dc_sub None 751"
  by (dc_eval dc_nc_0751)

lemma upt_nc_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma sec_nc_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding upt_nc_046 .
  then show "dc_sub None j" using dc_nc_0736 dc_nc_0737 dc_nc_0738 dc_nc_0739 dc_nc_0740 dc_nc_0741 dc_nc_0742 dc_nc_0743 dc_nc_0744 dc_nc_0745 dc_nc_0746 dc_nc_0747 dc_nc_0748 dc_nc_0749 dc_nc_0750 dc_nc_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
