theory GOCX_nc_176
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2816: "goc_sub None 2816"
  by (goc_eval goc_nc_2816)

lemma goc_nc_2817: "goc_sub None 2817"
  by (goc_eval goc_nc_2817)

lemma goc_nc_2818: "goc_sub None 2818"
  by (goc_eval goc_nc_2818)

lemma goc_nc_2819: "goc_sub None 2819"
  by (goc_eval goc_nc_2819)

lemma goc_nc_2820: "goc_sub None 2820"
  by (goc_eval goc_nc_2820)

lemma goc_nc_2821: "goc_sub None 2821"
  by (goc_eval goc_nc_2821)

lemma goc_nc_2822: "goc_sub None 2822"
  by (goc_eval goc_nc_2822)

lemma goc_nc_2823: "goc_sub None 2823"
  by (goc_eval goc_nc_2823)

lemma goc_nc_2824: "goc_sub None 2824"
  by (goc_eval goc_nc_2824)

lemma goc_nc_2825: "goc_sub None 2825"
  by (goc_eval goc_nc_2825)

lemma goc_nc_2826: "goc_sub None 2826"
  by (goc_eval goc_nc_2826)

lemma goc_nc_2827: "goc_sub None 2827"
  by (goc_eval goc_nc_2827)

lemma goc_nc_2828: "goc_sub None 2828"
  by (goc_eval goc_nc_2828)

lemma goc_nc_2829: "goc_sub None 2829"
  by (goc_eval goc_nc_2829)

lemma goc_nc_2830: "goc_sub None 2830"
  by (goc_eval goc_nc_2830)

lemma goc_nc_2831: "goc_sub None 2831"
  by (goc_eval goc_nc_2831)

lemma gupt_nc_176: "[2816..<2832] = [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]"
  by (simp add: upt_rec)

lemma gsec_nc_176: "\<forall>j\<in>{16 * 176..<16 * 176 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 176..<16 * 176 + 16}"
  then have "j \<in> set [2816..<2832]" unfolding set_upt by simp
  then have "j \<in> set [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]" unfolding gupt_nc_176 .
  then show "goc_sub None j" using goc_nc_2816 goc_nc_2817 goc_nc_2818 goc_nc_2819 goc_nc_2820 goc_nc_2821 goc_nc_2822 goc_nc_2823 goc_nc_2824 goc_nc_2825 goc_nc_2826 goc_nc_2827 goc_nc_2828 goc_nc_2829 goc_nc_2830 goc_nc_2831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
