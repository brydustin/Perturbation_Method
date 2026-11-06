theory OCX_nc_176
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2816: "oc_sub None 2816"
  by (oc_eval oc_nc_2816)

lemma oc_nc_2817: "oc_sub None 2817"
  by (oc_eval oc_nc_2817)

lemma oc_nc_2818: "oc_sub None 2818"
  by (oc_eval oc_nc_2818)

lemma oc_nc_2819: "oc_sub None 2819"
  by (oc_eval oc_nc_2819)

lemma oc_nc_2820: "oc_sub None 2820"
  by (oc_eval oc_nc_2820)

lemma oc_nc_2821: "oc_sub None 2821"
  by (oc_eval oc_nc_2821)

lemma oc_nc_2822: "oc_sub None 2822"
  by (oc_eval oc_nc_2822)

lemma oc_nc_2823: "oc_sub None 2823"
  by (oc_eval oc_nc_2823)

lemma oc_nc_2824: "oc_sub None 2824"
  by (oc_eval oc_nc_2824)

lemma oc_nc_2825: "oc_sub None 2825"
  by (oc_eval oc_nc_2825)

lemma oc_nc_2826: "oc_sub None 2826"
  by (oc_eval oc_nc_2826)

lemma oc_nc_2827: "oc_sub None 2827"
  by (oc_eval oc_nc_2827)

lemma oc_nc_2828: "oc_sub None 2828"
  by (oc_eval oc_nc_2828)

lemma oc_nc_2829: "oc_sub None 2829"
  by (oc_eval oc_nc_2829)

lemma oc_nc_2830: "oc_sub None 2830"
  by (oc_eval oc_nc_2830)

lemma oc_nc_2831: "oc_sub None 2831"
  by (oc_eval oc_nc_2831)

lemma upt_nc_176: "[2816..<2832] = [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]"
  by (simp add: upt_rec)

lemma sec_nc_176: "\<forall>j\<in>{16 * 176..<16 * 176 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 176..<16 * 176 + 16}"
  then have "j \<in> set [2816..<2832]" unfolding set_upt by simp
  then have "j \<in> set [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]" unfolding upt_nc_176 .
  then show "oc_sub None j" using oc_nc_2816 oc_nc_2817 oc_nc_2818 oc_nc_2819 oc_nc_2820 oc_nc_2821 oc_nc_2822 oc_nc_2823 oc_nc_2824 oc_nc_2825 oc_nc_2826 oc_nc_2827 oc_nc_2828 oc_nc_2829 oc_nc_2830 oc_nc_2831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
