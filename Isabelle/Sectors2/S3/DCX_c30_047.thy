theory DCX_c30_047
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0752: "dc_sub dc_b30 752"
  by (dc_eval dc_c30_0752)

lemma dc_c30_0753: "dc_sub dc_b30 753"
  by (dc_eval dc_c30_0753)

lemma dc_c30_0754: "dc_sub dc_b30 754"
  by (dc_eval dc_c30_0754)

lemma dc_c30_0755: "dc_sub dc_b30 755"
  by (dc_eval dc_c30_0755)

lemma dc_c30_0756: "dc_sub dc_b30 756"
  by (dc_eval dc_c30_0756)

lemma dc_c30_0757: "dc_sub dc_b30 757"
  by (dc_eval dc_c30_0757)

lemma dc_c30_0758: "dc_sub dc_b30 758"
  by (dc_eval dc_c30_0758)

lemma dc_c30_0759: "dc_sub dc_b30 759"
  by (dc_eval dc_c30_0759)

lemma dc_c30_0760: "dc_sub dc_b30 760"
  by (dc_eval dc_c30_0760)

lemma dc_c30_0761: "dc_sub dc_b30 761"
  by (dc_eval dc_c30_0761)

lemma dc_c30_0762: "dc_sub dc_b30 762"
  by (dc_eval dc_c30_0762)

lemma dc_c30_0763: "dc_sub dc_b30 763"
  by (dc_eval dc_c30_0763)

lemma dc_c30_0764: "dc_sub dc_b30 764"
  by (dc_eval dc_c30_0764)

lemma dc_c30_0765: "dc_sub dc_b30 765"
  by (dc_eval dc_c30_0765)

lemma dc_c30_0766: "dc_sub dc_b30 766"
  by (dc_eval dc_c30_0766)

lemma dc_c30_0767: "dc_sub dc_b30 767"
  by (dc_eval dc_c30_0767)

lemma upt_c30_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma sec_c30_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding upt_c30_047 .
  then show "dc_sub dc_b30 j" using dc_c30_0752 dc_c30_0753 dc_c30_0754 dc_c30_0755 dc_c30_0756 dc_c30_0757 dc_c30_0758 dc_c30_0759 dc_c30_0760 dc_c30_0761 dc_c30_0762 dc_c30_0763 dc_c30_0764 dc_c30_0765 dc_c30_0766 dc_c30_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
