theory OCX_nc_180
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2880: "oc_sub None 2880"
  by (oc_eval oc_nc_2880)

lemma oc_nc_2881: "oc_sub None 2881"
  by (oc_eval oc_nc_2881)

lemma oc_nc_2882: "oc_sub None 2882"
  by (oc_eval oc_nc_2882)

lemma oc_nc_2883: "oc_sub None 2883"
  by (oc_eval oc_nc_2883)

lemma oc_nc_2884: "oc_sub None 2884"
  by (oc_eval oc_nc_2884)

lemma oc_nc_2885: "oc_sub None 2885"
  by (oc_eval oc_nc_2885)

lemma oc_nc_2886: "oc_sub None 2886"
  by (oc_eval oc_nc_2886)

lemma oc_nc_2887: "oc_sub None 2887"
  by (oc_eval oc_nc_2887)

lemma oc_nc_2888: "oc_sub None 2888"
  by (oc_eval oc_nc_2888)

lemma oc_nc_2889: "oc_sub None 2889"
  by (oc_eval oc_nc_2889)

lemma oc_nc_2890: "oc_sub None 2890"
  by (oc_eval oc_nc_2890)

lemma oc_nc_2891: "oc_sub None 2891"
  by (oc_eval oc_nc_2891)

lemma oc_nc_2892: "oc_sub None 2892"
  by (oc_eval oc_nc_2892)

lemma oc_nc_2893: "oc_sub None 2893"
  by (oc_eval oc_nc_2893)

lemma oc_nc_2894: "oc_sub None 2894"
  by (oc_eval oc_nc_2894)

lemma oc_nc_2895: "oc_sub None 2895"
  by (oc_eval oc_nc_2895)

lemma upt_nc_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma sec_nc_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding upt_nc_180 .
  then show "oc_sub None j" using oc_nc_2880 oc_nc_2881 oc_nc_2882 oc_nc_2883 oc_nc_2884 oc_nc_2885 oc_nc_2886 oc_nc_2887 oc_nc_2888 oc_nc_2889 oc_nc_2890 oc_nc_2891 oc_nc_2892 oc_nc_2893 oc_nc_2894 oc_nc_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
