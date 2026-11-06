theory OCX_c30_046
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0736: "oc_sub oc_b30 736"
  by (oc_eval oc_c30_0736)

lemma oc_c30_0737: "oc_sub oc_b30 737"
  by (oc_eval oc_c30_0737)

lemma oc_c30_0738: "oc_sub oc_b30 738"
  by (oc_eval oc_c30_0738)

lemma oc_c30_0739: "oc_sub oc_b30 739"
  by (oc_eval oc_c30_0739)

lemma oc_c30_0740: "oc_sub oc_b30 740"
  by (oc_eval oc_c30_0740)

lemma oc_c30_0741: "oc_sub oc_b30 741"
  by (oc_eval oc_c30_0741)

lemma oc_c30_0742: "oc_sub oc_b30 742"
  by (oc_eval oc_c30_0742)

lemma oc_c30_0743: "oc_sub oc_b30 743"
  by (oc_eval oc_c30_0743)

lemma oc_c30_0744: "oc_sub oc_b30 744"
  by (oc_eval oc_c30_0744)

lemma oc_c30_0745: "oc_sub oc_b30 745"
  by (oc_eval oc_c30_0745)

lemma oc_c30_0746: "oc_sub oc_b30 746"
  by (oc_eval oc_c30_0746)

lemma oc_c30_0747: "oc_sub oc_b30 747"
  by (oc_eval oc_c30_0747)

lemma oc_c30_0748: "oc_sub oc_b30 748"
  by (oc_eval oc_c30_0748)

lemma oc_c30_0749: "oc_sub oc_b30 749"
  by (oc_eval oc_c30_0749)

lemma oc_c30_0750: "oc_sub oc_b30 750"
  by (oc_eval oc_c30_0750)

lemma oc_c30_0751: "oc_sub oc_b30 751"
  by (oc_eval oc_c30_0751)

lemma upt_c30_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma sec_c30_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding upt_c30_046 .
  then show "oc_sub oc_b30 j" using oc_c30_0736 oc_c30_0737 oc_c30_0738 oc_c30_0739 oc_c30_0740 oc_c30_0741 oc_c30_0742 oc_c30_0743 oc_c30_0744 oc_c30_0745 oc_c30_0746 oc_c30_0747 oc_c30_0748 oc_c30_0749 oc_c30_0750 oc_c30_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
