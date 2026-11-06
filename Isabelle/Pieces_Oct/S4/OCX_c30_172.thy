theory OCX_c30_172
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2752: "oc_sub oc_b30 2752"
  by (oc_eval oc_c30_2752)

lemma oc_c30_2753: "oc_sub oc_b30 2753"
  by (oc_eval oc_c30_2753)

lemma oc_c30_2754: "oc_sub oc_b30 2754"
  by (oc_eval oc_c30_2754)

lemma oc_c30_2755: "oc_sub oc_b30 2755"
  by (oc_eval oc_c30_2755)

lemma oc_c30_2756: "oc_sub oc_b30 2756"
  by (oc_eval oc_c30_2756)

lemma oc_c30_2757: "oc_sub oc_b30 2757"
  by (oc_eval oc_c30_2757)

lemma oc_c30_2758: "oc_sub oc_b30 2758"
  by (oc_eval oc_c30_2758)

lemma oc_c30_2759: "oc_sub oc_b30 2759"
  by (oc_eval oc_c30_2759)

lemma oc_c30_2760: "oc_sub oc_b30 2760"
  by (oc_eval oc_c30_2760)

lemma oc_c30_2761: "oc_sub oc_b30 2761"
  by (oc_eval oc_c30_2761)

lemma oc_c30_2762: "oc_sub oc_b30 2762"
  by (oc_eval oc_c30_2762)

lemma oc_c30_2763: "oc_sub oc_b30 2763"
  by (oc_eval oc_c30_2763)

lemma oc_c30_2764: "oc_sub oc_b30 2764"
  by (oc_eval oc_c30_2764)

lemma oc_c30_2765: "oc_sub oc_b30 2765"
  by (oc_eval oc_c30_2765)

lemma oc_c30_2766: "oc_sub oc_b30 2766"
  by (oc_eval oc_c30_2766)

lemma oc_c30_2767: "oc_sub oc_b30 2767"
  by (oc_eval oc_c30_2767)

lemma upt_c30_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma sec_c30_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding upt_c30_172 .
  then show "oc_sub oc_b30 j" using oc_c30_2752 oc_c30_2753 oc_c30_2754 oc_c30_2755 oc_c30_2756 oc_c30_2757 oc_c30_2758 oc_c30_2759 oc_c30_2760 oc_c30_2761 oc_c30_2762 oc_c30_2763 oc_c30_2764 oc_c30_2765 oc_c30_2766 oc_c30_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
