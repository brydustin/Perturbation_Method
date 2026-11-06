theory GOCX_nc_046
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0736: "goc_sub None 736"
  by (goc_eval goc_nc_0736)

lemma goc_nc_0737: "goc_sub None 737"
  by (goc_eval goc_nc_0737)

lemma goc_nc_0738: "goc_sub None 738"
  by (goc_eval goc_nc_0738)

lemma goc_nc_0739: "goc_sub None 739"
  by (goc_eval goc_nc_0739)

lemma goc_nc_0740: "goc_sub None 740"
  by (goc_eval goc_nc_0740)

lemma goc_nc_0741: "goc_sub None 741"
  by (goc_eval goc_nc_0741)

lemma goc_nc_0742: "goc_sub None 742"
  by (goc_eval goc_nc_0742)

lemma goc_nc_0743: "goc_sub None 743"
  by (goc_eval goc_nc_0743)

lemma goc_nc_0744: "goc_sub None 744"
  by (goc_eval goc_nc_0744)

lemma goc_nc_0745: "goc_sub None 745"
  by (goc_eval goc_nc_0745)

lemma goc_nc_0746: "goc_sub None 746"
  by (goc_eval goc_nc_0746)

lemma goc_nc_0747: "goc_sub None 747"
  by (goc_eval goc_nc_0747)

lemma goc_nc_0748: "goc_sub None 748"
  by (goc_eval goc_nc_0748)

lemma goc_nc_0749: "goc_sub None 749"
  by (goc_eval goc_nc_0749)

lemma goc_nc_0750: "goc_sub None 750"
  by (goc_eval goc_nc_0750)

lemma goc_nc_0751: "goc_sub None 751"
  by (goc_eval goc_nc_0751)

lemma gupt_nc_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma gsec_nc_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding gupt_nc_046 .
  then show "goc_sub None j" using goc_nc_0736 goc_nc_0737 goc_nc_0738 goc_nc_0739 goc_nc_0740 goc_nc_0741 goc_nc_0742 goc_nc_0743 goc_nc_0744 goc_nc_0745 goc_nc_0746 goc_nc_0747 goc_nc_0748 goc_nc_0749 goc_nc_0750 goc_nc_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
