theory GDCX_nc_180
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2880: "gdc_sub None 2880"
  by (gdc_eval gdc_nc_2880)

lemma gdc_nc_2881: "gdc_sub None 2881"
  by (gdc_eval gdc_nc_2881)

lemma gdc_nc_2882: "gdc_sub None 2882"
  by (gdc_eval gdc_nc_2882)

lemma gdc_nc_2883: "gdc_sub None 2883"
  by (gdc_eval gdc_nc_2883)

lemma gdc_nc_2884: "gdc_sub None 2884"
  by (gdc_eval gdc_nc_2884)

lemma gdc_nc_2885: "gdc_sub None 2885"
  by (gdc_eval gdc_nc_2885)

lemma gdc_nc_2886: "gdc_sub None 2886"
  by (gdc_eval gdc_nc_2886)

lemma gdc_nc_2887: "gdc_sub None 2887"
  by (gdc_eval gdc_nc_2887)

lemma gdc_nc_2888: "gdc_sub None 2888"
  by (gdc_eval gdc_nc_2888)

lemma gdc_nc_2889: "gdc_sub None 2889"
  by (gdc_eval gdc_nc_2889)

lemma gdc_nc_2890: "gdc_sub None 2890"
  by (gdc_eval gdc_nc_2890)

lemma gdc_nc_2891: "gdc_sub None 2891"
  by (gdc_eval gdc_nc_2891)

lemma gdc_nc_2892: "gdc_sub None 2892"
  by (gdc_eval gdc_nc_2892)

lemma gdc_nc_2893: "gdc_sub None 2893"
  by (gdc_eval gdc_nc_2893)

lemma gdc_nc_2894: "gdc_sub None 2894"
  by (gdc_eval gdc_nc_2894)

lemma gdc_nc_2895: "gdc_sub None 2895"
  by (gdc_eval gdc_nc_2895)

lemma gupt_nc_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma gsec_nc_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding gupt_nc_180 .
  then show "gdc_sub None j" using gdc_nc_2880 gdc_nc_2881 gdc_nc_2882 gdc_nc_2883 gdc_nc_2884 gdc_nc_2885 gdc_nc_2886 gdc_nc_2887 gdc_nc_2888 gdc_nc_2889 gdc_nc_2890 gdc_nc_2891 gdc_nc_2892 gdc_nc_2893 gdc_nc_2894 gdc_nc_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
