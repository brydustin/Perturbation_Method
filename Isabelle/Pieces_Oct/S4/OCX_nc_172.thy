theory OCX_nc_172
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2752: "oc_sub None 2752"
  by (oc_eval oc_nc_2752)

lemma oc_nc_2753: "oc_sub None 2753"
  by (oc_eval oc_nc_2753)

lemma oc_nc_2754: "oc_sub None 2754"
  by (oc_eval oc_nc_2754)

lemma oc_nc_2755: "oc_sub None 2755"
  by (oc_eval oc_nc_2755)

lemma oc_nc_2756: "oc_sub None 2756"
  by (oc_eval oc_nc_2756)

lemma oc_nc_2757: "oc_sub None 2757"
  by (oc_eval oc_nc_2757)

lemma oc_nc_2758: "oc_sub None 2758"
  by (oc_eval oc_nc_2758)

lemma oc_nc_2759: "oc_sub None 2759"
  by (oc_eval oc_nc_2759)

lemma oc_nc_2760: "oc_sub None 2760"
  by (oc_eval oc_nc_2760)

lemma oc_nc_2761: "oc_sub None 2761"
  by (oc_eval oc_nc_2761)

lemma oc_nc_2762: "oc_sub None 2762"
  by (oc_eval oc_nc_2762)

lemma oc_nc_2763: "oc_sub None 2763"
  by (oc_eval oc_nc_2763)

lemma oc_nc_2764: "oc_sub None 2764"
  by (oc_eval oc_nc_2764)

lemma oc_nc_2765: "oc_sub None 2765"
  by (oc_eval oc_nc_2765)

lemma oc_nc_2766: "oc_sub None 2766"
  by (oc_eval oc_nc_2766)

lemma oc_nc_2767: "oc_sub None 2767"
  by (oc_eval oc_nc_2767)

lemma upt_nc_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma sec_nc_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding upt_nc_172 .
  then show "oc_sub None j" using oc_nc_2752 oc_nc_2753 oc_nc_2754 oc_nc_2755 oc_nc_2756 oc_nc_2757 oc_nc_2758 oc_nc_2759 oc_nc_2760 oc_nc_2761 oc_nc_2762 oc_nc_2763 oc_nc_2764 oc_nc_2765 oc_nc_2766 oc_nc_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
