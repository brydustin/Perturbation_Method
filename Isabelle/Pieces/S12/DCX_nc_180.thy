theory DCX_nc_180
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2880: "dc_sub None 2880"
  by (dc_eval dc_nc_2880)

lemma dc_nc_2881: "dc_sub None 2881"
  by (dc_eval dc_nc_2881)

lemma dc_nc_2882: "dc_sub None 2882"
  by (dc_eval dc_nc_2882)

lemma dc_nc_2883: "dc_sub None 2883"
  by (dc_eval dc_nc_2883)

lemma dc_nc_2884: "dc_sub None 2884"
  by (dc_eval dc_nc_2884)

lemma dc_nc_2885: "dc_sub None 2885"
  by (dc_eval dc_nc_2885)

lemma dc_nc_2886: "dc_sub None 2886"
  by (dc_eval dc_nc_2886)

lemma dc_nc_2887: "dc_sub None 2887"
  by (dc_eval dc_nc_2887)

lemma dc_nc_2888: "dc_sub None 2888"
  by (dc_eval dc_nc_2888)

lemma dc_nc_2889: "dc_sub None 2889"
  by (dc_eval dc_nc_2889)

lemma dc_nc_2890: "dc_sub None 2890"
  by (dc_eval dc_nc_2890)

lemma dc_nc_2891: "dc_sub None 2891"
  by (dc_eval dc_nc_2891)

lemma dc_nc_2892: "dc_sub None 2892"
  by (dc_eval dc_nc_2892)

lemma dc_nc_2893: "dc_sub None 2893"
  by (dc_eval dc_nc_2893)

lemma dc_nc_2894: "dc_sub None 2894"
  by (dc_eval dc_nc_2894)

lemma dc_nc_2895: "dc_sub None 2895"
  by (dc_eval dc_nc_2895)

lemma upt_nc_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma sec_nc_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding upt_nc_180 .
  then show "dc_sub None j" using dc_nc_2880 dc_nc_2881 dc_nc_2882 dc_nc_2883 dc_nc_2884 dc_nc_2885 dc_nc_2886 dc_nc_2887 dc_nc_2888 dc_nc_2889 dc_nc_2890 dc_nc_2891 dc_nc_2892 dc_nc_2893 dc_nc_2894 dc_nc_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
