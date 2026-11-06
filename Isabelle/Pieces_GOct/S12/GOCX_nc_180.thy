theory GOCX_nc_180
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2880: "goc_sub None 2880"
  by (goc_eval goc_nc_2880)

lemma goc_nc_2881: "goc_sub None 2881"
  by (goc_eval goc_nc_2881)

lemma goc_nc_2882: "goc_sub None 2882"
  by (goc_eval goc_nc_2882)

lemma goc_nc_2883: "goc_sub None 2883"
  by (goc_eval goc_nc_2883)

lemma goc_nc_2884: "goc_sub None 2884"
  by (goc_eval goc_nc_2884)

lemma goc_nc_2885: "goc_sub None 2885"
  by (goc_eval goc_nc_2885)

lemma goc_nc_2886: "goc_sub None 2886"
  by (goc_eval goc_nc_2886)

lemma goc_nc_2887: "goc_sub None 2887"
  by (goc_eval goc_nc_2887)

lemma goc_nc_2888: "goc_sub None 2888"
  by (goc_eval goc_nc_2888)

lemma goc_nc_2889: "goc_sub None 2889"
  by (goc_eval goc_nc_2889)

lemma goc_nc_2890: "goc_sub None 2890"
  by (goc_eval goc_nc_2890)

lemma goc_nc_2891: "goc_sub None 2891"
  by (goc_eval goc_nc_2891)

lemma goc_nc_2892: "goc_sub None 2892"
  by (goc_eval goc_nc_2892)

lemma goc_nc_2893: "goc_sub None 2893"
  by (goc_eval goc_nc_2893)

lemma goc_nc_2894: "goc_sub None 2894"
  by (goc_eval goc_nc_2894)

lemma goc_nc_2895: "goc_sub None 2895"
  by (goc_eval goc_nc_2895)

lemma gupt_nc_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma gsec_nc_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding gupt_nc_180 .
  then show "goc_sub None j" using goc_nc_2880 goc_nc_2881 goc_nc_2882 goc_nc_2883 goc_nc_2884 goc_nc_2885 goc_nc_2886 goc_nc_2887 goc_nc_2888 goc_nc_2889 goc_nc_2890 goc_nc_2891 goc_nc_2892 goc_nc_2893 goc_nc_2894 goc_nc_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
