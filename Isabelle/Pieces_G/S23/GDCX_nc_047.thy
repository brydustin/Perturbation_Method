theory GDCX_nc_047
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0752: "gdc_sub None 752"
  by (gdc_eval gdc_nc_0752)

lemma gdc_nc_0753: "gdc_sub None 753"
  by (gdc_eval gdc_nc_0753)

lemma gdc_nc_0754: "gdc_sub None 754"
  by (gdc_eval gdc_nc_0754)

lemma gdc_nc_0755: "gdc_sub None 755"
  by (gdc_eval gdc_nc_0755)

lemma gdc_nc_0756: "gdc_sub None 756"
  by (gdc_eval gdc_nc_0756)

lemma gdc_nc_0757: "gdc_sub None 757"
  by (gdc_eval gdc_nc_0757)

lemma gdc_nc_0758: "gdc_sub None 758"
  by (gdc_eval gdc_nc_0758)

lemma gdc_nc_0759: "gdc_sub None 759"
  by (gdc_eval gdc_nc_0759)

lemma gdc_nc_0760: "gdc_sub None 760"
  by (gdc_eval gdc_nc_0760)

lemma gdc_nc_0761: "gdc_sub None 761"
  by (gdc_eval gdc_nc_0761)

lemma gdc_nc_0762: "gdc_sub None 762"
  by (gdc_eval gdc_nc_0762)

lemma gdc_nc_0763: "gdc_sub None 763"
  by (gdc_eval gdc_nc_0763)

lemma gdc_nc_0764: "gdc_sub None 764"
  by (gdc_eval gdc_nc_0764)

lemma gdc_nc_0765: "gdc_sub None 765"
  by (gdc_eval gdc_nc_0765)

lemma gdc_nc_0766: "gdc_sub None 766"
  by (gdc_eval gdc_nc_0766)

lemma gdc_nc_0767: "gdc_sub None 767"
  by (gdc_eval gdc_nc_0767)

lemma gupt_nc_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma gsec_nc_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding gupt_nc_047 .
  then show "gdc_sub None j" using gdc_nc_0752 gdc_nc_0753 gdc_nc_0754 gdc_nc_0755 gdc_nc_0756 gdc_nc_0757 gdc_nc_0758 gdc_nc_0759 gdc_nc_0760 gdc_nc_0761 gdc_nc_0762 gdc_nc_0763 gdc_nc_0764 gdc_nc_0765 gdc_nc_0766 gdc_nc_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
