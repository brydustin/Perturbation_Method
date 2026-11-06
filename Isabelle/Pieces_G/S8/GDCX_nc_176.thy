theory GDCX_nc_176
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2816: "gdc_sub None 2816"
  by (gdc_eval gdc_nc_2816)

lemma gdc_nc_2817: "gdc_sub None 2817"
  by (gdc_eval gdc_nc_2817)

lemma gdc_nc_2818: "gdc_sub None 2818"
  by (gdc_eval gdc_nc_2818)

lemma gdc_nc_2819: "gdc_sub None 2819"
  by (gdc_eval gdc_nc_2819)

lemma gdc_nc_2820: "gdc_sub None 2820"
  by (gdc_eval gdc_nc_2820)

lemma gdc_nc_2821: "gdc_sub None 2821"
  by (gdc_eval gdc_nc_2821)

lemma gdc_nc_2822: "gdc_sub None 2822"
  by (gdc_eval gdc_nc_2822)

lemma gdc_nc_2823: "gdc_sub None 2823"
  by (gdc_eval gdc_nc_2823)

lemma gdc_nc_2824: "gdc_sub None 2824"
  by (gdc_eval gdc_nc_2824)

lemma gdc_nc_2825: "gdc_sub None 2825"
  by (gdc_eval gdc_nc_2825)

lemma gdc_nc_2826: "gdc_sub None 2826"
  by (gdc_eval gdc_nc_2826)

lemma gdc_nc_2827: "gdc_sub None 2827"
  by (gdc_eval gdc_nc_2827)

lemma gdc_nc_2828: "gdc_sub None 2828"
  by (gdc_eval gdc_nc_2828)

lemma gdc_nc_2829: "gdc_sub None 2829"
  by (gdc_eval gdc_nc_2829)

lemma gdc_nc_2830: "gdc_sub None 2830"
  by (gdc_eval gdc_nc_2830)

lemma gdc_nc_2831: "gdc_sub None 2831"
  by (gdc_eval gdc_nc_2831)

lemma gupt_nc_176: "[2816..<2832] = [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]"
  by (simp add: upt_rec)

lemma gsec_nc_176: "\<forall>j\<in>{16 * 176..<16 * 176 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 176..<16 * 176 + 16}"
  then have "j \<in> set [2816..<2832]" unfolding set_upt by simp
  then have "j \<in> set [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]" unfolding gupt_nc_176 .
  then show "gdc_sub None j" using gdc_nc_2816 gdc_nc_2817 gdc_nc_2818 gdc_nc_2819 gdc_nc_2820 gdc_nc_2821 gdc_nc_2822 gdc_nc_2823 gdc_nc_2824 gdc_nc_2825 gdc_nc_2826 gdc_nc_2827 gdc_nc_2828 gdc_nc_2829 gdc_nc_2830 gdc_nc_2831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
