theory OCX_c30_047
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0752: "oc_sub oc_b30 752"
  by (oc_eval oc_c30_0752)

lemma oc_c30_0753: "oc_sub oc_b30 753"
  by (oc_eval oc_c30_0753)

lemma oc_c30_0754: "oc_sub oc_b30 754"
  by (oc_eval oc_c30_0754)

lemma oc_c30_0755: "oc_sub oc_b30 755"
  by (oc_eval oc_c30_0755)

lemma oc_c30_0756: "oc_sub oc_b30 756"
  by (oc_eval oc_c30_0756)

lemma oc_c30_0757: "oc_sub oc_b30 757"
  by (oc_eval oc_c30_0757)

lemma oc_c30_0758: "oc_sub oc_b30 758"
  by (oc_eval oc_c30_0758)

lemma oc_c30_0759: "oc_sub oc_b30 759"
  by (oc_eval oc_c30_0759)

lemma oc_c30_0760: "oc_sub oc_b30 760"
  by (oc_eval oc_c30_0760)

lemma oc_c30_0761: "oc_sub oc_b30 761"
  by (oc_eval oc_c30_0761)

lemma oc_c30_0762: "oc_sub oc_b30 762"
  by (oc_eval oc_c30_0762)

lemma oc_c30_0763: "oc_sub oc_b30 763"
  by (oc_eval oc_c30_0763)

lemma oc_c30_0764: "oc_sub oc_b30 764"
  by (oc_eval oc_c30_0764)

lemma oc_c30_0765: "oc_sub oc_b30 765"
  by (oc_eval oc_c30_0765)

lemma oc_c30_0766: "oc_sub oc_b30 766"
  by (oc_eval oc_c30_0766)

lemma oc_c30_0767: "oc_sub oc_b30 767"
  by (oc_eval oc_c30_0767)

lemma upt_c30_047: "[752..<768] = [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]"
  by (simp add: upt_rec)

lemma sec_c30_047: "\<forall>j\<in>{16 * 47..<16 * 47 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 47..<16 * 47 + 16}"
  then have "j \<in> set [752..<768]" unfolding set_upt by simp
  then have "j \<in> set [752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]" unfolding upt_c30_047 .
  then show "oc_sub oc_b30 j" using oc_c30_0752 oc_c30_0753 oc_c30_0754 oc_c30_0755 oc_c30_0756 oc_c30_0757 oc_c30_0758 oc_c30_0759 oc_c30_0760 oc_c30_0761 oc_c30_0762 oc_c30_0763 oc_c30_0764 oc_c30_0765 oc_c30_0766 oc_c30_0767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
