theory GOCX_nc_047
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0752: "goc_sub None 752"
  by (goc_eval goc_nc_0752)

lemma goc_nc_0753: "goc_sub None 753"
  by (goc_eval goc_nc_0753)

lemma goc_nc_0754: "goc_sub None 754"
  by (goc_eval goc_nc_0754)

lemma goc_nc_0755: "goc_sub None 755"
  by (goc_eval goc_nc_0755)

lemma goc_nc_0756: "goc_sub None 756"
  by (goc_eval goc_nc_0756)

lemma goc_nc_0757: "goc_sub None 757"
  by (goc_eval goc_nc_0757)

lemma goc_nc_0758: "goc_sub None 758"
  by (goc_eval goc_nc_0758)

lemma goc_nc_0759: "goc_sub None 759"
  by (goc_eval goc_nc_0759)

lemma goc_nc_0760: "goc_sub None 760"
  by (goc_eval goc_nc_0760)

lemma goc_nc_0761: "goc_sub None 761"
  by (goc_eval goc_nc_0761)

lemma goc_nc_0762: "goc_sub None 762"
  by (goc_eval goc_nc_0762)

lemma goc_nc_0763: "goc_sub None 763"
  by (goc_eval goc_nc_0763)

lemma goc_nc_0764: "goc_sub None 764"
  by (goc_eval goc_nc_0764)

lemma goc_nc_0765: "goc_sub None 765"
  by (goc_eval goc_nc_0765)

lemma goc_nc_0766: "goc_sub None 766"
  by (goc_eval goc_nc_0766)

lemma goc_nc_0767: "goc_sub None 767"
  by (goc_eval goc_nc_0767)

lemma gupt_nc_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma gsec_nc_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding gupt_nc_047 .
  then show "goc_sub None j" using goc_nc_0752 goc_nc_0753 goc_nc_0754 goc_nc_0755 goc_nc_0756 goc_nc_0757 goc_nc_0758 goc_nc_0759 goc_nc_0760 goc_nc_0761 goc_nc_0762 goc_nc_0763 goc_nc_0764 goc_nc_0765 goc_nc_0766 goc_nc_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
