theory OCX_nc_051
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0816: "oc_sub None 816"
  by (oc_eval oc_nc_0816)

lemma oc_nc_0817: "oc_sub None 817"
  by (oc_eval oc_nc_0817)

lemma oc_nc_0818: "oc_sub None 818"
  by (oc_eval oc_nc_0818)

lemma oc_nc_0819: "oc_sub None 819"
  by (oc_eval oc_nc_0819)

lemma oc_nc_0820: "oc_sub None 820"
  by (oc_eval oc_nc_0820)

lemma oc_nc_0821: "oc_sub None 821"
  by (oc_eval oc_nc_0821)

lemma oc_nc_0822: "oc_sub None 822"
  by (oc_eval oc_nc_0822)

lemma oc_nc_0823: "oc_sub None 823"
  by (oc_eval oc_nc_0823)

lemma oc_nc_0824: "oc_sub None 824"
  by (oc_eval oc_nc_0824)

lemma oc_nc_0825: "oc_sub None 825"
  by (oc_eval oc_nc_0825)

lemma oc_nc_0826: "oc_sub None 826"
  by (oc_eval oc_nc_0826)

lemma oc_nc_0827: "oc_sub None 827"
  by (oc_eval oc_nc_0827)

lemma oc_nc_0828: "oc_sub None 828"
  by (oc_eval oc_nc_0828)

lemma oc_nc_0829: "oc_sub None 829"
  by (oc_eval oc_nc_0829)

lemma oc_nc_0830: "oc_sub None 830"
  by (oc_eval oc_nc_0830)

lemma oc_nc_0831: "oc_sub None 831"
  by (oc_eval oc_nc_0831)

lemma upt_nc_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma sec_nc_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding upt_nc_051 .
  then show "oc_sub None j" using oc_nc_0816 oc_nc_0817 oc_nc_0818 oc_nc_0819 oc_nc_0820 oc_nc_0821 oc_nc_0822 oc_nc_0823 oc_nc_0824 oc_nc_0825 oc_nc_0826 oc_nc_0827 oc_nc_0828 oc_nc_0829 oc_nc_0830 oc_nc_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
