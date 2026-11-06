theory DCX_c30_055
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0880: "dc_sub dc_b30 880"
  by (dc_eval dc_c30_0880)

lemma dc_c30_0881: "dc_sub dc_b30 881"
  by (dc_eval dc_c30_0881)

lemma dc_c30_0882: "dc_sub dc_b30 882"
  by (dc_eval dc_c30_0882)

lemma dc_c30_0883: "dc_sub dc_b30 883"
  by (dc_eval dc_c30_0883)

lemma dc_c30_0884: "dc_sub dc_b30 884"
  by (dc_eval dc_c30_0884)

lemma dc_c30_0885: "dc_sub dc_b30 885"
  by (dc_eval dc_c30_0885)

lemma dc_c30_0886: "dc_sub dc_b30 886"
  by (dc_eval dc_c30_0886)

lemma dc_c30_0887: "dc_sub dc_b30 887"
  by (dc_eval dc_c30_0887)

lemma dc_c30_0888: "dc_sub dc_b30 888"
  by (dc_eval dc_c30_0888)

lemma dc_c30_0889: "dc_sub dc_b30 889"
  by (dc_eval dc_c30_0889)

lemma dc_c30_0890: "dc_sub dc_b30 890"
  by (dc_eval dc_c30_0890)

lemma dc_c30_0891: "dc_sub dc_b30 891"
  by (dc_eval dc_c30_0891)

lemma dc_c30_0892: "dc_sub dc_b30 892"
  by (dc_eval dc_c30_0892)

lemma dc_c30_0893: "dc_sub dc_b30 893"
  by (dc_eval dc_c30_0893)

lemma dc_c30_0894: "dc_sub dc_b30 894"
  by (dc_eval dc_c30_0894)

lemma dc_c30_0895: "dc_sub dc_b30 895"
  by (dc_eval dc_c30_0895)

lemma upt_c30_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma sec_c30_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding upt_c30_055 .
  then show "dc_sub dc_b30 j" using dc_c30_0880 dc_c30_0881 dc_c30_0882 dc_c30_0883 dc_c30_0884 dc_c30_0885 dc_c30_0886 dc_c30_0887 dc_c30_0888 dc_c30_0889 dc_c30_0890 dc_c30_0891 dc_c30_0892 dc_c30_0893 dc_c30_0894 dc_c30_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
