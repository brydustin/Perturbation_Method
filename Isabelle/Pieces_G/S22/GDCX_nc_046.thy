theory GDCX_nc_046
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0736: "gdc_sub None 736"
  by (gdc_eval gdc_nc_0736)

lemma gdc_nc_0737: "gdc_sub None 737"
  by (gdc_eval gdc_nc_0737)

lemma gdc_nc_0738: "gdc_sub None 738"
  by (gdc_eval gdc_nc_0738)

lemma gdc_nc_0739: "gdc_sub None 739"
  by (gdc_eval gdc_nc_0739)

lemma gdc_nc_0740: "gdc_sub None 740"
  by (gdc_eval gdc_nc_0740)

lemma gdc_nc_0741: "gdc_sub None 741"
  by (gdc_eval gdc_nc_0741)

lemma gdc_nc_0742: "gdc_sub None 742"
  by (gdc_eval gdc_nc_0742)

lemma gdc_nc_0743: "gdc_sub None 743"
  by (gdc_eval gdc_nc_0743)

lemma gdc_nc_0744: "gdc_sub None 744"
  by (gdc_eval gdc_nc_0744)

lemma gdc_nc_0745: "gdc_sub None 745"
  by (gdc_eval gdc_nc_0745)

lemma gdc_nc_0746: "gdc_sub None 746"
  by (gdc_eval gdc_nc_0746)

lemma gdc_nc_0747: "gdc_sub None 747"
  by (gdc_eval gdc_nc_0747)

lemma gdc_nc_0748: "gdc_sub None 748"
  by (gdc_eval gdc_nc_0748)

lemma gdc_nc_0749: "gdc_sub None 749"
  by (gdc_eval gdc_nc_0749)

lemma gdc_nc_0750: "gdc_sub None 750"
  by (gdc_eval gdc_nc_0750)

lemma gdc_nc_0751: "gdc_sub None 751"
  by (gdc_eval gdc_nc_0751)

lemma gupt_nc_046: "[736..<752] = [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]"
  by (simp add: upt_rec)

lemma gsec_nc_046: "\<forall>j\<in>{16 * 46..<16 * 46 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 46..<16 * 46 + 16}"
  then have "j \<in> set [736..<752]" unfolding set_upt by simp
  then have "j \<in> set [736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]" unfolding gupt_nc_046 .
  then show "gdc_sub None j" using gdc_nc_0736 gdc_nc_0737 gdc_nc_0738 gdc_nc_0739 gdc_nc_0740 gdc_nc_0741 gdc_nc_0742 gdc_nc_0743 gdc_nc_0744 gdc_nc_0745 gdc_nc_0746 gdc_nc_0747 gdc_nc_0748 gdc_nc_0749 gdc_nc_0750 gdc_nc_0751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
