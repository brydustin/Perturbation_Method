theory OCX_c30_176
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2816: "oc_sub oc_b30 2816"
  by (oc_eval oc_c30_2816)

lemma oc_c30_2817: "oc_sub oc_b30 2817"
  by (oc_eval oc_c30_2817)

lemma oc_c30_2818: "oc_sub oc_b30 2818"
  by (oc_eval oc_c30_2818)

lemma oc_c30_2819: "oc_sub oc_b30 2819"
  by (oc_eval oc_c30_2819)

lemma oc_c30_2820: "oc_sub oc_b30 2820"
  by (oc_eval oc_c30_2820)

lemma oc_c30_2821: "oc_sub oc_b30 2821"
  by (oc_eval oc_c30_2821)

lemma oc_c30_2822: "oc_sub oc_b30 2822"
  by (oc_eval oc_c30_2822)

lemma oc_c30_2823: "oc_sub oc_b30 2823"
  by (oc_eval oc_c30_2823)

lemma oc_c30_2824: "oc_sub oc_b30 2824"
  by (oc_eval oc_c30_2824)

lemma oc_c30_2825: "oc_sub oc_b30 2825"
  by (oc_eval oc_c30_2825)

lemma oc_c30_2826: "oc_sub oc_b30 2826"
  by (oc_eval oc_c30_2826)

lemma oc_c30_2827: "oc_sub oc_b30 2827"
  by (oc_eval oc_c30_2827)

lemma oc_c30_2828: "oc_sub oc_b30 2828"
  by (oc_eval oc_c30_2828)

lemma oc_c30_2829: "oc_sub oc_b30 2829"
  by (oc_eval oc_c30_2829)

lemma oc_c30_2830: "oc_sub oc_b30 2830"
  by (oc_eval oc_c30_2830)

lemma oc_c30_2831: "oc_sub oc_b30 2831"
  by (oc_eval oc_c30_2831)

lemma upt_c30_176: "[2816..<2832] = [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]"
  by (simp add: upt_rec)

lemma sec_c30_176: "\<forall>j\<in>{16 * 176..<16 * 176 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 176..<16 * 176 + 16}"
  then have "j \<in> set [2816..<2832]" unfolding set_upt by simp
  then have "j \<in> set [2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]" unfolding upt_c30_176 .
  then show "oc_sub oc_b30 j" using oc_c30_2816 oc_c30_2817 oc_c30_2818 oc_c30_2819 oc_c30_2820 oc_c30_2821 oc_c30_2822 oc_c30_2823 oc_c30_2824 oc_c30_2825 oc_c30_2826 oc_c30_2827 oc_c30_2828 oc_c30_2829 oc_c30_2830 oc_c30_2831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
