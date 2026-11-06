theory DCX_c30_051
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0816: "dc_sub dc_b30 816"
  by (dc_eval dc_c30_0816)

lemma dc_c30_0817: "dc_sub dc_b30 817"
  by (dc_eval dc_c30_0817)

lemma dc_c30_0818: "dc_sub dc_b30 818"
  by (dc_eval dc_c30_0818)

lemma dc_c30_0819: "dc_sub dc_b30 819"
  by (dc_eval dc_c30_0819)

lemma dc_c30_0820: "dc_sub dc_b30 820"
  by (dc_eval dc_c30_0820)

lemma dc_c30_0821: "dc_sub dc_b30 821"
  by (dc_eval dc_c30_0821)

lemma dc_c30_0822: "dc_sub dc_b30 822"
  by (dc_eval dc_c30_0822)

lemma dc_c30_0823: "dc_sub dc_b30 823"
  by (dc_eval dc_c30_0823)

lemma dc_c30_0824: "dc_sub dc_b30 824"
  by (dc_eval dc_c30_0824)

lemma dc_c30_0825: "dc_sub dc_b30 825"
  by (dc_eval dc_c30_0825)

lemma dc_c30_0826: "dc_sub dc_b30 826"
  by (dc_eval dc_c30_0826)

lemma dc_c30_0827: "dc_sub dc_b30 827"
  by (dc_eval dc_c30_0827)

lemma dc_c30_0828: "dc_sub dc_b30 828"
  by (dc_eval dc_c30_0828)

lemma dc_c30_0829: "dc_sub dc_b30 829"
  by (dc_eval dc_c30_0829)

lemma dc_c30_0830: "dc_sub dc_b30 830"
  by (dc_eval dc_c30_0830)

lemma dc_c30_0831: "dc_sub dc_b30 831"
  by (dc_eval dc_c30_0831)

lemma upt_c30_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma sec_c30_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding upt_c30_051 .
  then show "dc_sub dc_b30 j" using dc_c30_0816 dc_c30_0817 dc_c30_0818 dc_c30_0819 dc_c30_0820 dc_c30_0821 dc_c30_0822 dc_c30_0823 dc_c30_0824 dc_c30_0825 dc_c30_0826 dc_c30_0827 dc_c30_0828 dc_c30_0829 dc_c30_0830 dc_c30_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
