theory DCX_nc_051
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0816: "dc_sub None 816"
  by (dc_eval dc_nc_0816)

lemma dc_nc_0817: "dc_sub None 817"
  by (dc_eval dc_nc_0817)

lemma dc_nc_0818: "dc_sub None 818"
  by (dc_eval dc_nc_0818)

lemma dc_nc_0819: "dc_sub None 819"
  by (dc_eval dc_nc_0819)

lemma dc_nc_0820: "dc_sub None 820"
  by (dc_eval dc_nc_0820)

lemma dc_nc_0821: "dc_sub None 821"
  by (dc_eval dc_nc_0821)

lemma dc_nc_0822: "dc_sub None 822"
  by (dc_eval dc_nc_0822)

lemma dc_nc_0823: "dc_sub None 823"
  by (dc_eval dc_nc_0823)

lemma dc_nc_0824: "dc_sub None 824"
  by (dc_eval dc_nc_0824)

lemma dc_nc_0825: "dc_sub None 825"
  by (dc_eval dc_nc_0825)

lemma dc_nc_0826: "dc_sub None 826"
  by (dc_eval dc_nc_0826)

lemma dc_nc_0827: "dc_sub None 827"
  by (dc_eval dc_nc_0827)

lemma dc_nc_0828: "dc_sub None 828"
  by (dc_eval dc_nc_0828)

lemma dc_nc_0829: "dc_sub None 829"
  by (dc_eval dc_nc_0829)

lemma dc_nc_0830: "dc_sub None 830"
  by (dc_eval dc_nc_0830)

lemma dc_nc_0831: "dc_sub None 831"
  by (dc_eval dc_nc_0831)

lemma upt_nc_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma sec_nc_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding upt_nc_051 .
  then show "dc_sub None j" using dc_nc_0816 dc_nc_0817 dc_nc_0818 dc_nc_0819 dc_nc_0820 dc_nc_0821 dc_nc_0822 dc_nc_0823 dc_nc_0824 dc_nc_0825 dc_nc_0826 dc_nc_0827 dc_nc_0828 dc_nc_0829 dc_nc_0830 dc_nc_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
