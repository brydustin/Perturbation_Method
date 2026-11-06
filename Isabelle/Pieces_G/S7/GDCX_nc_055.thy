theory GDCX_nc_055
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0880: "gdc_sub None 880"
  by (gdc_eval gdc_nc_0880)

lemma gdc_nc_0881: "gdc_sub None 881"
  by (gdc_eval gdc_nc_0881)

lemma gdc_nc_0882: "gdc_sub None 882"
  by (gdc_eval gdc_nc_0882)

lemma gdc_nc_0883: "gdc_sub None 883"
  by (gdc_eval gdc_nc_0883)

lemma gdc_nc_0884: "gdc_sub None 884"
  by (gdc_eval gdc_nc_0884)

lemma gdc_nc_0885: "gdc_sub None 885"
  by (gdc_eval gdc_nc_0885)

lemma gdc_nc_0886: "gdc_sub None 886"
  by (gdc_eval gdc_nc_0886)

lemma gdc_nc_0887: "gdc_sub None 887"
  by (gdc_eval gdc_nc_0887)

lemma gdc_nc_0888: "gdc_sub None 888"
  by (gdc_eval gdc_nc_0888)

lemma gdc_nc_0889: "gdc_sub None 889"
  by (gdc_eval gdc_nc_0889)

lemma gdc_nc_0890: "gdc_sub None 890"
  by (gdc_eval gdc_nc_0890)

lemma gdc_nc_0891: "gdc_sub None 891"
  by (gdc_eval gdc_nc_0891)

lemma gdc_nc_0892: "gdc_sub None 892"
  by (gdc_eval gdc_nc_0892)

lemma gdc_nc_0893: "gdc_sub None 893"
  by (gdc_eval gdc_nc_0893)

lemma gdc_nc_0894: "gdc_sub None 894"
  by (gdc_eval gdc_nc_0894)

lemma gdc_nc_0895: "gdc_sub None 895"
  by (gdc_eval gdc_nc_0895)

lemma gupt_nc_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma gsec_nc_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding gupt_nc_055 .
  then show "gdc_sub None j" using gdc_nc_0880 gdc_nc_0881 gdc_nc_0882 gdc_nc_0883 gdc_nc_0884 gdc_nc_0885 gdc_nc_0886 gdc_nc_0887 gdc_nc_0888 gdc_nc_0889 gdc_nc_0890 gdc_nc_0891 gdc_nc_0892 gdc_nc_0893 gdc_nc_0894 gdc_nc_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
