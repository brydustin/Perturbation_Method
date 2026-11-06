theory DCX_nc_047
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0752: "dc_sub None 752"
  by (dc_eval dc_nc_0752)

lemma dc_nc_0753: "dc_sub None 753"
  by (dc_eval dc_nc_0753)

lemma dc_nc_0754: "dc_sub None 754"
  by (dc_eval dc_nc_0754)

lemma dc_nc_0755: "dc_sub None 755"
  by (dc_eval dc_nc_0755)

lemma dc_nc_0756: "dc_sub None 756"
  by (dc_eval dc_nc_0756)

lemma dc_nc_0757: "dc_sub None 757"
  by (dc_eval dc_nc_0757)

lemma dc_nc_0758: "dc_sub None 758"
  by (dc_eval dc_nc_0758)

lemma dc_nc_0759: "dc_sub None 759"
  by (dc_eval dc_nc_0759)

lemma dc_nc_0760: "dc_sub None 760"
  by (dc_eval dc_nc_0760)

lemma dc_nc_0761: "dc_sub None 761"
  by (dc_eval dc_nc_0761)

lemma dc_nc_0762: "dc_sub None 762"
  by (dc_eval dc_nc_0762)

lemma dc_nc_0763: "dc_sub None 763"
  by (dc_eval dc_nc_0763)

lemma dc_nc_0764: "dc_sub None 764"
  by (dc_eval dc_nc_0764)

lemma dc_nc_0765: "dc_sub None 765"
  by (dc_eval dc_nc_0765)

lemma dc_nc_0766: "dc_sub None 766"
  by (dc_eval dc_nc_0766)

lemma dc_nc_0767: "dc_sub None 767"
  by (dc_eval dc_nc_0767)

lemma upt_nc_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma sec_nc_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding upt_nc_047 .
  then show "dc_sub None j" using dc_nc_0752 dc_nc_0753 dc_nc_0754 dc_nc_0755 dc_nc_0756 dc_nc_0757 dc_nc_0758 dc_nc_0759 dc_nc_0760 dc_nc_0761 dc_nc_0762 dc_nc_0763 dc_nc_0764 dc_nc_0765 dc_nc_0766 dc_nc_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
