theory OCX_c30_051
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0816: "oc_sub oc_b30 816"
  by (oc_eval oc_c30_0816)

lemma oc_c30_0817: "oc_sub oc_b30 817"
  by (oc_eval oc_c30_0817)

lemma oc_c30_0818: "oc_sub oc_b30 818"
  by (oc_eval oc_c30_0818)

lemma oc_c30_0819: "oc_sub oc_b30 819"
  by (oc_eval oc_c30_0819)

lemma oc_c30_0820: "oc_sub oc_b30 820"
  by (oc_eval oc_c30_0820)

lemma oc_c30_0821: "oc_sub oc_b30 821"
  by (oc_eval oc_c30_0821)

lemma oc_c30_0822: "oc_sub oc_b30 822"
  by (oc_eval oc_c30_0822)

lemma oc_c30_0823: "oc_sub oc_b30 823"
  by (oc_eval oc_c30_0823)

lemma oc_c30_0824: "oc_sub oc_b30 824"
  by (oc_eval oc_c30_0824)

lemma oc_c30_0825: "oc_sub oc_b30 825"
  by (oc_eval oc_c30_0825)

lemma oc_c30_0826: "oc_sub oc_b30 826"
  by (oc_eval oc_c30_0826)

lemma oc_c30_0827: "oc_sub oc_b30 827"
  by (oc_eval oc_c30_0827)

lemma oc_c30_0828: "oc_sub oc_b30 828"
  by (oc_eval oc_c30_0828)

lemma oc_c30_0829: "oc_sub oc_b30 829"
  by (oc_eval oc_c30_0829)

lemma oc_c30_0830: "oc_sub oc_b30 830"
  by (oc_eval oc_c30_0830)

lemma oc_c30_0831: "oc_sub oc_b30 831"
  by (oc_eval oc_c30_0831)

lemma upt_c30_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma sec_c30_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding upt_c30_051 .
  then show "oc_sub oc_b30 j" using oc_c30_0816 oc_c30_0817 oc_c30_0818 oc_c30_0819 oc_c30_0820 oc_c30_0821 oc_c30_0822 oc_c30_0823 oc_c30_0824 oc_c30_0825 oc_c30_0826 oc_c30_0827 oc_c30_0828 oc_c30_0829 oc_c30_0830 oc_c30_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
