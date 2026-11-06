theory DCX_nc_172
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2752: "dc_sub None 2752"
  by (dc_eval dc_nc_2752)

lemma dc_nc_2753: "dc_sub None 2753"
  by (dc_eval dc_nc_2753)

lemma dc_nc_2754: "dc_sub None 2754"
  by (dc_eval dc_nc_2754)

lemma dc_nc_2755: "dc_sub None 2755"
  by (dc_eval dc_nc_2755)

lemma dc_nc_2756: "dc_sub None 2756"
  by (dc_eval dc_nc_2756)

lemma dc_nc_2757: "dc_sub None 2757"
  by (dc_eval dc_nc_2757)

lemma dc_nc_2758: "dc_sub None 2758"
  by (dc_eval dc_nc_2758)

lemma dc_nc_2759: "dc_sub None 2759"
  by (dc_eval dc_nc_2759)

lemma dc_nc_2760: "dc_sub None 2760"
  by (dc_eval dc_nc_2760)

lemma dc_nc_2761: "dc_sub None 2761"
  by (dc_eval dc_nc_2761)

lemma dc_nc_2762: "dc_sub None 2762"
  by (dc_eval dc_nc_2762)

lemma dc_nc_2763: "dc_sub None 2763"
  by (dc_eval dc_nc_2763)

lemma dc_nc_2764: "dc_sub None 2764"
  by (dc_eval dc_nc_2764)

lemma dc_nc_2765: "dc_sub None 2765"
  by (dc_eval dc_nc_2765)

lemma dc_nc_2766: "dc_sub None 2766"
  by (dc_eval dc_nc_2766)

lemma dc_nc_2767: "dc_sub None 2767"
  by (dc_eval dc_nc_2767)

lemma upt_nc_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma sec_nc_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding upt_nc_172 .
  then show "dc_sub None j" using dc_nc_2752 dc_nc_2753 dc_nc_2754 dc_nc_2755 dc_nc_2756 dc_nc_2757 dc_nc_2758 dc_nc_2759 dc_nc_2760 dc_nc_2761 dc_nc_2762 dc_nc_2763 dc_nc_2764 dc_nc_2765 dc_nc_2766 dc_nc_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
