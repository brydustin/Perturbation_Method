theory DCX_c30_180
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2880: "dc_sub dc_b30 2880"
  by (dc_eval dc_c30_2880)

lemma dc_c30_2881: "dc_sub dc_b30 2881"
  by (dc_eval dc_c30_2881)

lemma dc_c30_2882: "dc_sub dc_b30 2882"
  by (dc_eval dc_c30_2882)

lemma dc_c30_2883: "dc_sub dc_b30 2883"
  by (dc_eval dc_c30_2883)

lemma dc_c30_2884: "dc_sub dc_b30 2884"
  by (dc_eval dc_c30_2884)

lemma dc_c30_2885: "dc_sub dc_b30 2885"
  by (dc_eval dc_c30_2885)

lemma dc_c30_2886: "dc_sub dc_b30 2886"
  by (dc_eval dc_c30_2886)

lemma dc_c30_2887: "dc_sub dc_b30 2887"
  by (dc_eval dc_c30_2887)

lemma dc_c30_2888: "dc_sub dc_b30 2888"
  by (dc_eval dc_c30_2888)

lemma dc_c30_2889: "dc_sub dc_b30 2889"
  by (dc_eval dc_c30_2889)

lemma dc_c30_2890: "dc_sub dc_b30 2890"
  by (dc_eval dc_c30_2890)

lemma dc_c30_2891: "dc_sub dc_b30 2891"
  by (dc_eval dc_c30_2891)

lemma dc_c30_2892: "dc_sub dc_b30 2892"
  by (dc_eval dc_c30_2892)

lemma dc_c30_2893: "dc_sub dc_b30 2893"
  by (dc_eval dc_c30_2893)

lemma dc_c30_2894: "dc_sub dc_b30 2894"
  by (dc_eval dc_c30_2894)

lemma dc_c30_2895: "dc_sub dc_b30 2895"
  by (dc_eval dc_c30_2895)

lemma upt_c30_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma sec_c30_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding upt_c30_180 .
  then show "dc_sub dc_b30 j" using dc_c30_2880 dc_c30_2881 dc_c30_2882 dc_c30_2883 dc_c30_2884 dc_c30_2885 dc_c30_2886 dc_c30_2887 dc_c30_2888 dc_c30_2889 dc_c30_2890 dc_c30_2891 dc_c30_2892 dc_c30_2893 dc_c30_2894 dc_c30_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
