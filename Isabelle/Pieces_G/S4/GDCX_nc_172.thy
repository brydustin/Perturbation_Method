theory GDCX_nc_172
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2752: "gdc_sub None 2752"
  by (gdc_eval gdc_nc_2752)

lemma gdc_nc_2753: "gdc_sub None 2753"
  by (gdc_eval gdc_nc_2753)

lemma gdc_nc_2754: "gdc_sub None 2754"
  by (gdc_eval gdc_nc_2754)

lemma gdc_nc_2755: "gdc_sub None 2755"
  by (gdc_eval gdc_nc_2755)

lemma gdc_nc_2756: "gdc_sub None 2756"
  by (gdc_eval gdc_nc_2756)

lemma gdc_nc_2757: "gdc_sub None 2757"
  by (gdc_eval gdc_nc_2757)

lemma gdc_nc_2758: "gdc_sub None 2758"
  by (gdc_eval gdc_nc_2758)

lemma gdc_nc_2759: "gdc_sub None 2759"
  by (gdc_eval gdc_nc_2759)

lemma gdc_nc_2760: "gdc_sub None 2760"
  by (gdc_eval gdc_nc_2760)

lemma gdc_nc_2761: "gdc_sub None 2761"
  by (gdc_eval gdc_nc_2761)

lemma gdc_nc_2762: "gdc_sub None 2762"
  by (gdc_eval gdc_nc_2762)

lemma gdc_nc_2763: "gdc_sub None 2763"
  by (gdc_eval gdc_nc_2763)

lemma gdc_nc_2764: "gdc_sub None 2764"
  by (gdc_eval gdc_nc_2764)

lemma gdc_nc_2765: "gdc_sub None 2765"
  by (gdc_eval gdc_nc_2765)

lemma gdc_nc_2766: "gdc_sub None 2766"
  by (gdc_eval gdc_nc_2766)

lemma gdc_nc_2767: "gdc_sub None 2767"
  by (gdc_eval gdc_nc_2767)

lemma gupt_nc_172: "[2752..<2768] = [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]"
  by (simp add: upt_rec)

lemma gsec_nc_172: "\<forall>j\<in>{16 * 172..<16 * 172 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 172..<16 * 172 + 16}"
  then have "j \<in> set [2752..<2768]" unfolding set_upt by simp
  then have "j \<in> set [2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767]" unfolding gupt_nc_172 .
  then show "gdc_sub None j" using gdc_nc_2752 gdc_nc_2753 gdc_nc_2754 gdc_nc_2755 gdc_nc_2756 gdc_nc_2757 gdc_nc_2758 gdc_nc_2759 gdc_nc_2760 gdc_nc_2761 gdc_nc_2762 gdc_nc_2763 gdc_nc_2764 gdc_nc_2765 gdc_nc_2766 gdc_nc_2767
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
