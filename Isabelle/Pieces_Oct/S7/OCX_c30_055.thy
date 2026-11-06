theory OCX_c30_055
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0880: "oc_sub oc_b30 880"
  by (oc_eval oc_c30_0880)

lemma oc_c30_0881: "oc_sub oc_b30 881"
  by (oc_eval oc_c30_0881)

lemma oc_c30_0882: "oc_sub oc_b30 882"
  by (oc_eval oc_c30_0882)

lemma oc_c30_0883: "oc_sub oc_b30 883"
  by (oc_eval oc_c30_0883)

lemma oc_c30_0884: "oc_sub oc_b30 884"
  by (oc_eval oc_c30_0884)

lemma oc_c30_0885: "oc_sub oc_b30 885"
  by (oc_eval oc_c30_0885)

lemma oc_c30_0886: "oc_sub oc_b30 886"
  by (oc_eval oc_c30_0886)

lemma oc_c30_0887: "oc_sub oc_b30 887"
  by (oc_eval oc_c30_0887)

lemma oc_c30_0888: "oc_sub oc_b30 888"
  by (oc_eval oc_c30_0888)

lemma oc_c30_0889: "oc_sub oc_b30 889"
  by (oc_eval oc_c30_0889)

lemma oc_c30_0890: "oc_sub oc_b30 890"
  by (oc_eval oc_c30_0890)

lemma oc_c30_0891: "oc_sub oc_b30 891"
  by (oc_eval oc_c30_0891)

lemma oc_c30_0892: "oc_sub oc_b30 892"
  by (oc_eval oc_c30_0892)

lemma oc_c30_0893: "oc_sub oc_b30 893"
  by (oc_eval oc_c30_0893)

lemma oc_c30_0894: "oc_sub oc_b30 894"
  by (oc_eval oc_c30_0894)

lemma oc_c30_0895: "oc_sub oc_b30 895"
  by (oc_eval oc_c30_0895)

lemma upt_c30_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma sec_c30_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding upt_c30_055 .
  then show "oc_sub oc_b30 j" using oc_c30_0880 oc_c30_0881 oc_c30_0882 oc_c30_0883 oc_c30_0884 oc_c30_0885 oc_c30_0886 oc_c30_0887 oc_c30_0888 oc_c30_0889 oc_c30_0890 oc_c30_0891 oc_c30_0892 oc_c30_0893 oc_c30_0894 oc_c30_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
