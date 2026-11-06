theory OCX_nc_047
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0752: "oc_sub None 752"
  by (oc_eval oc_nc_0752)

lemma oc_nc_0753: "oc_sub None 753"
  by (oc_eval oc_nc_0753)

lemma oc_nc_0754: "oc_sub None 754"
  by (oc_eval oc_nc_0754)

lemma oc_nc_0755: "oc_sub None 755"
  by (oc_eval oc_nc_0755)

lemma oc_nc_0756: "oc_sub None 756"
  by (oc_eval oc_nc_0756)

lemma oc_nc_0757: "oc_sub None 757"
  by (oc_eval oc_nc_0757)

lemma oc_nc_0758: "oc_sub None 758"
  by (oc_eval oc_nc_0758)

lemma oc_nc_0759: "oc_sub None 759"
  by (oc_eval oc_nc_0759)

lemma oc_nc_0760: "oc_sub None 760"
  by (oc_eval oc_nc_0760)

lemma oc_nc_0761: "oc_sub None 761"
  by (oc_eval oc_nc_0761)

lemma oc_nc_0762: "oc_sub None 762"
  by (oc_eval oc_nc_0762)

lemma oc_nc_0763: "oc_sub None 763"
  by (oc_eval oc_nc_0763)

lemma oc_nc_0764: "oc_sub None 764"
  by (oc_eval oc_nc_0764)

lemma oc_nc_0765: "oc_sub None 765"
  by (oc_eval oc_nc_0765)

lemma oc_nc_0766: "oc_sub None 766"
  by (oc_eval oc_nc_0766)

lemma oc_nc_0767: "oc_sub None 767"
  by (oc_eval oc_nc_0767)

lemma upt_nc_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma sec_nc_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding upt_nc_047 .
  then show "oc_sub None j" using oc_nc_0752 oc_nc_0753 oc_nc_0754 oc_nc_0755 oc_nc_0756 oc_nc_0757 oc_nc_0758 oc_nc_0759 oc_nc_0760 oc_nc_0761 oc_nc_0762 oc_nc_0763 oc_nc_0764 oc_nc_0765 oc_nc_0766 oc_nc_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
