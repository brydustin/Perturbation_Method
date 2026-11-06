theory DCX_nc_055
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0880: "dc_sub None 880"
  by (dc_eval dc_nc_0880)

lemma dc_nc_0881: "dc_sub None 881"
  by (dc_eval dc_nc_0881)

lemma dc_nc_0882: "dc_sub None 882"
  by (dc_eval dc_nc_0882)

lemma dc_nc_0883: "dc_sub None 883"
  by (dc_eval dc_nc_0883)

lemma dc_nc_0884: "dc_sub None 884"
  by (dc_eval dc_nc_0884)

lemma dc_nc_0885: "dc_sub None 885"
  by (dc_eval dc_nc_0885)

lemma dc_nc_0886: "dc_sub None 886"
  by (dc_eval dc_nc_0886)

lemma dc_nc_0887: "dc_sub None 887"
  by (dc_eval dc_nc_0887)

lemma dc_nc_0888: "dc_sub None 888"
  by (dc_eval dc_nc_0888)

lemma dc_nc_0889: "dc_sub None 889"
  by (dc_eval dc_nc_0889)

lemma dc_nc_0890: "dc_sub None 890"
  by (dc_eval dc_nc_0890)

lemma dc_nc_0891: "dc_sub None 891"
  by (dc_eval dc_nc_0891)

lemma dc_nc_0892: "dc_sub None 892"
  by (dc_eval dc_nc_0892)

lemma dc_nc_0893: "dc_sub None 893"
  by (dc_eval dc_nc_0893)

lemma dc_nc_0894: "dc_sub None 894"
  by (dc_eval dc_nc_0894)

lemma dc_nc_0895: "dc_sub None 895"
  by (dc_eval dc_nc_0895)

lemma upt_nc_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma sec_nc_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding upt_nc_055 .
  then show "dc_sub None j" using dc_nc_0880 dc_nc_0881 dc_nc_0882 dc_nc_0883 dc_nc_0884 dc_nc_0885 dc_nc_0886 dc_nc_0887 dc_nc_0888 dc_nc_0889 dc_nc_0890 dc_nc_0891 dc_nc_0892 dc_nc_0893 dc_nc_0894 dc_nc_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
