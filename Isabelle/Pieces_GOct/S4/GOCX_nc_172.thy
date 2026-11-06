theory GOCX_nc_172
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2752: "goc_sub None 2752"
  by (goc_eval goc_nc_2752)

lemma goc_nc_2753: "goc_sub None 2753"
  by (goc_eval goc_nc_2753)

lemma goc_nc_2754: "goc_sub None 2754"
  by (goc_eval goc_nc_2754)

lemma goc_nc_2755: "goc_sub None 2755"
  by (goc_eval goc_nc_2755)

lemma goc_nc_2756: "goc_sub None 2756"
  by (goc_eval goc_nc_2756)

lemma goc_nc_2757: "goc_sub None 2757"
  by (goc_eval goc_nc_2757)

lemma goc_nc_2758: "goc_sub None 2758"
  by (goc_eval goc_nc_2758)

lemma goc_nc_2759: "goc_sub None 2759"
  by (goc_eval goc_nc_2759)

lemma goc_nc_2760: "goc_sub None 2760"
  by (goc_eval goc_nc_2760)

lemma goc_nc_2761: "goc_sub None 2761"
  by (goc_eval goc_nc_2761)

lemma goc_nc_2762: "goc_sub None 2762"
  by (goc_eval goc_nc_2762)

lemma goc_nc_2763: "goc_sub None 2763"
  by (goc_eval goc_nc_2763)

lemma goc_nc_2764: "goc_sub None 2764"
  by (goc_eval goc_nc_2764)

lemma goc_nc_2765: "goc_sub None 2765"
  by (goc_eval goc_nc_2765)

lemma goc_nc_2766: "goc_sub None 2766"
  by (goc_eval goc_nc_2766)

lemma goc_nc_2767: "goc_sub None 2767"
  by (goc_eval goc_nc_2767)

lemma gupt_nc_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma gsec_nc_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding gupt_nc_172 .
  then show "goc_sub None j" using goc_nc_2752 goc_nc_2753 goc_nc_2754 goc_nc_2755 goc_nc_2756 goc_nc_2757 goc_nc_2758 goc_nc_2759 goc_nc_2760 goc_nc_2761 goc_nc_2762 goc_nc_2763 goc_nc_2764 goc_nc_2765 goc_nc_2766 goc_nc_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
