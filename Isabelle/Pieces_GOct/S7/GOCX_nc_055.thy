theory GOCX_nc_055
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0880: "goc_sub None 880"
  by (goc_eval goc_nc_0880)

lemma goc_nc_0881: "goc_sub None 881"
  by (goc_eval goc_nc_0881)

lemma goc_nc_0882: "goc_sub None 882"
  by (goc_eval goc_nc_0882)

lemma goc_nc_0883: "goc_sub None 883"
  by (goc_eval goc_nc_0883)

lemma goc_nc_0884: "goc_sub None 884"
  by (goc_eval goc_nc_0884)

lemma goc_nc_0885: "goc_sub None 885"
  by (goc_eval goc_nc_0885)

lemma goc_nc_0886: "goc_sub None 886"
  by (goc_eval goc_nc_0886)

lemma goc_nc_0887: "goc_sub None 887"
  by (goc_eval goc_nc_0887)

lemma goc_nc_0888: "goc_sub None 888"
  by (goc_eval goc_nc_0888)

lemma goc_nc_0889: "goc_sub None 889"
  by (goc_eval goc_nc_0889)

lemma goc_nc_0890: "goc_sub None 890"
  by (goc_eval goc_nc_0890)

lemma goc_nc_0891: "goc_sub None 891"
  by (goc_eval goc_nc_0891)

lemma goc_nc_0892: "goc_sub None 892"
  by (goc_eval goc_nc_0892)

lemma goc_nc_0893: "goc_sub None 893"
  by (goc_eval goc_nc_0893)

lemma goc_nc_0894: "goc_sub None 894"
  by (goc_eval goc_nc_0894)

lemma goc_nc_0895: "goc_sub None 895"
  by (goc_eval goc_nc_0895)

lemma gupt_nc_055: "[880..<896] = [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]"
  by (simp add: upt_rec)

lemma gsec_nc_055: "\<forall>j\<in>{16 * 55..<16 * 55 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 55..<16 * 55 + 16}"
  then have "j \<in> set [880..<896]" unfolding set_upt by simp
  then have "j \<in> set [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]" unfolding gupt_nc_055 .
  then show "goc_sub None j" using goc_nc_0880 goc_nc_0881 goc_nc_0882 goc_nc_0883 goc_nc_0884 goc_nc_0885 goc_nc_0886 goc_nc_0887 goc_nc_0888 goc_nc_0889 goc_nc_0890 goc_nc_0891 goc_nc_0892 goc_nc_0893 goc_nc_0894 goc_nc_0895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
