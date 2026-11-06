theory DCX_nc_176
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2816: "dc_sub None 2816"
  by (dc_eval dc_nc_2816)

lemma dc_nc_2817: "dc_sub None 2817"
  by (dc_eval dc_nc_2817)

lemma dc_nc_2818: "dc_sub None 2818"
  by (dc_eval dc_nc_2818)

lemma dc_nc_2819: "dc_sub None 2819"
  by (dc_eval dc_nc_2819)

lemma dc_nc_2820: "dc_sub None 2820"
  by (dc_eval dc_nc_2820)

lemma dc_nc_2821: "dc_sub None 2821"
  by (dc_eval dc_nc_2821)

lemma dc_nc_2822: "dc_sub None 2822"
  by (dc_eval dc_nc_2822)

lemma dc_nc_2823: "dc_sub None 2823"
  by (dc_eval dc_nc_2823)

lemma dc_nc_2824: "dc_sub None 2824"
  by (dc_eval dc_nc_2824)

lemma dc_nc_2825: "dc_sub None 2825"
  by (dc_eval dc_nc_2825)

lemma dc_nc_2826: "dc_sub None 2826"
  by (dc_eval dc_nc_2826)

lemma dc_nc_2827: "dc_sub None 2827"
  by (dc_eval dc_nc_2827)

lemma dc_nc_2828: "dc_sub None 2828"
  by (dc_eval dc_nc_2828)

lemma dc_nc_2829: "dc_sub None 2829"
  by (dc_eval dc_nc_2829)

lemma dc_nc_2830: "dc_sub None 2830"
  by (dc_eval dc_nc_2830)

lemma dc_nc_2831: "dc_sub None 2831"
  by (dc_eval dc_nc_2831)

lemma upt_nc_176: "[2816..<2832] = [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]"
  by (simp add: upt_rec)

lemma sec_nc_176: "\<forall>j\<in>{16 * 176..<16 * 176 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 176..<16 * 176 + 16}"
  then have "j \<in> set [2816..<2832]" unfolding set_upt by simp
  then have "j \<in> set [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]" unfolding upt_nc_176 .
  then show "dc_sub None j" using dc_nc_2816 dc_nc_2817 dc_nc_2818 dc_nc_2819 dc_nc_2820 dc_nc_2821 dc_nc_2822 dc_nc_2823 dc_nc_2824 dc_nc_2825 dc_nc_2826 dc_nc_2827 dc_nc_2828 dc_nc_2829 dc_nc_2830 dc_nc_2831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
