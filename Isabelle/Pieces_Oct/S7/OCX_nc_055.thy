theory OCX_nc_055
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0880: "oc_sub None 880"
  by (oc_eval oc_nc_0880)

lemma oc_nc_0881: "oc_sub None 881"
  by (oc_eval oc_nc_0881)

lemma oc_nc_0882: "oc_sub None 882"
  by (oc_eval oc_nc_0882)

lemma oc_nc_0883: "oc_sub None 883"
  by (oc_eval oc_nc_0883)

lemma oc_nc_0884: "oc_sub None 884"
  by (oc_eval oc_nc_0884)

lemma oc_nc_0885: "oc_sub None 885"
  by (oc_eval oc_nc_0885)

lemma oc_nc_0886: "oc_sub None 886"
  by (oc_eval oc_nc_0886)

lemma oc_nc_0887: "oc_sub None 887"
  by (oc_eval oc_nc_0887)

lemma oc_nc_0888: "oc_sub None 888"
  by (oc_eval oc_nc_0888)

lemma oc_nc_0889: "oc_sub None 889"
  by (oc_eval oc_nc_0889)

lemma oc_nc_0890: "oc_sub None 890"
  by (oc_eval oc_nc_0890)

lemma oc_nc_0891: "oc_sub None 891"
  by (oc_eval oc_nc_0891)

lemma oc_nc_0892: "oc_sub None 892"
  by (oc_eval oc_nc_0892)

lemma oc_nc_0893: "oc_sub None 893"
  by (oc_eval oc_nc_0893)

lemma oc_nc_0894: "oc_sub None 894"
  by (oc_eval oc_nc_0894)

lemma oc_nc_0895: "oc_sub None 895"
  by (oc_eval oc_nc_0895)

lemma upt_nc_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma sec_nc_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding upt_nc_055 .
  then show "oc_sub None j" using oc_nc_0880 oc_nc_0881 oc_nc_0882 oc_nc_0883 oc_nc_0884 oc_nc_0885 oc_nc_0886 oc_nc_0887 oc_nc_0888 oc_nc_0889 oc_nc_0890 oc_nc_0891 oc_nc_0892 oc_nc_0893 oc_nc_0894 oc_nc_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
