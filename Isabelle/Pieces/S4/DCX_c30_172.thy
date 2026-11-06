theory DCX_c30_172
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2752: "dc_sub dc_b30 2752"
  by (dc_eval dc_c30_2752)

lemma dc_c30_2753: "dc_sub dc_b30 2753"
  by (dc_eval dc_c30_2753)

lemma dc_c30_2754: "dc_sub dc_b30 2754"
  by (dc_eval dc_c30_2754)

lemma dc_c30_2755: "dc_sub dc_b30 2755"
  by (dc_eval dc_c30_2755)

lemma dc_c30_2756: "dc_sub dc_b30 2756"
  by (dc_eval dc_c30_2756)

lemma dc_c30_2757: "dc_sub dc_b30 2757"
  by (dc_eval dc_c30_2757)

lemma dc_c30_2758: "dc_sub dc_b30 2758"
  by (dc_eval dc_c30_2758)

lemma dc_c30_2759: "dc_sub dc_b30 2759"
  by (dc_eval dc_c30_2759)

lemma dc_c30_2760: "dc_sub dc_b30 2760"
  by (dc_eval dc_c30_2760)

lemma dc_c30_2761: "dc_sub dc_b30 2761"
  by (dc_eval dc_c30_2761)

lemma dc_c30_2762: "dc_sub dc_b30 2762"
  by (dc_eval dc_c30_2762)

lemma dc_c30_2763: "dc_sub dc_b30 2763"
  by (dc_eval dc_c30_2763)

lemma dc_c30_2764: "dc_sub dc_b30 2764"
  by (dc_eval dc_c30_2764)

lemma dc_c30_2765: "dc_sub dc_b30 2765"
  by (dc_eval dc_c30_2765)

lemma dc_c30_2766: "dc_sub dc_b30 2766"
  by (dc_eval dc_c30_2766)

lemma dc_c30_2767: "dc_sub dc_b30 2767"
  by (dc_eval dc_c30_2767)

lemma upt_c30_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma sec_c30_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding upt_c30_172 .
  then show "dc_sub dc_b30 j" using dc_c30_2752 dc_c30_2753 dc_c30_2754 dc_c30_2755 dc_c30_2756 dc_c30_2757 dc_c30_2758 dc_c30_2759 dc_c30_2760 dc_c30_2761 dc_c30_2762 dc_c30_2763 dc_c30_2764 dc_c30_2765 dc_c30_2766 dc_c30_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
