theory DCX_c30_046
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0736: "dc_sub dc_b30 736"
  by (dc_eval dc_c30_0736)

lemma dc_c30_0737: "dc_sub dc_b30 737"
  by (dc_eval dc_c30_0737)

lemma dc_c30_0738: "dc_sub dc_b30 738"
  by (dc_eval dc_c30_0738)

lemma dc_c30_0739: "dc_sub dc_b30 739"
  by (dc_eval dc_c30_0739)

lemma dc_c30_0740: "dc_sub dc_b30 740"
  by (dc_eval dc_c30_0740)

lemma dc_c30_0741: "dc_sub dc_b30 741"
  by (dc_eval dc_c30_0741)

lemma dc_c30_0742: "dc_sub dc_b30 742"
  by (dc_eval dc_c30_0742)

lemma dc_c30_0743: "dc_sub dc_b30 743"
  by (dc_eval dc_c30_0743)

lemma dc_c30_0744: "dc_sub dc_b30 744"
  by (dc_eval dc_c30_0744)

lemma dc_c30_0745: "dc_sub dc_b30 745"
  by (dc_eval dc_c30_0745)

lemma dc_c30_0746: "dc_sub dc_b30 746"
  by (dc_eval dc_c30_0746)

lemma dc_c30_0747: "dc_sub dc_b30 747"
  by (dc_eval dc_c30_0747)

lemma dc_c30_0748: "dc_sub dc_b30 748"
  by (dc_eval dc_c30_0748)

lemma dc_c30_0749: "dc_sub dc_b30 749"
  by (dc_eval dc_c30_0749)

lemma dc_c30_0750: "dc_sub dc_b30 750"
  by (dc_eval dc_c30_0750)

lemma dc_c30_0751: "dc_sub dc_b30 751"
  by (dc_eval dc_c30_0751)

lemma upt_c30_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma sec_c30_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding upt_c30_046 .
  then show "dc_sub dc_b30 j" using dc_c30_0736 dc_c30_0737 dc_c30_0738 dc_c30_0739 dc_c30_0740 dc_c30_0741 dc_c30_0742 dc_c30_0743 dc_c30_0744 dc_c30_0745 dc_c30_0746 dc_c30_0747 dc_c30_0748 dc_c30_0749 dc_c30_0750 dc_c30_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
