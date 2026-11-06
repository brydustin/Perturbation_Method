theory GDCX_nc_054
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0864: "gdc_sub None 864"
  by (gdc_eval gdc_nc_0864)

lemma gdc_nc_0865: "gdc_sub None 865"
  by (gdc_eval gdc_nc_0865)

lemma gdc_nc_0866: "gdc_sub None 866"
  by (gdc_eval gdc_nc_0866)

lemma gdc_nc_0867: "gdc_sub None 867"
  by (gdc_eval gdc_nc_0867)

lemma gdc_nc_0868: "gdc_sub None 868"
  by (gdc_eval gdc_nc_0868)

lemma gdc_nc_0869: "gdc_sub None 869"
  by (gdc_eval gdc_nc_0869)

lemma gdc_nc_0870: "gdc_sub None 870"
  by (gdc_eval gdc_nc_0870)

lemma gdc_nc_0871: "gdc_sub None 871"
  by (gdc_eval gdc_nc_0871)

lemma gdc_nc_0872: "gdc_sub None 872"
  by (gdc_eval gdc_nc_0872)

lemma gdc_nc_0873: "gdc_sub None 873"
  by (gdc_eval gdc_nc_0873)

lemma gdc_nc_0874: "gdc_sub None 874"
  by (gdc_eval gdc_nc_0874)

lemma gdc_nc_0875: "gdc_sub None 875"
  by (gdc_eval gdc_nc_0875)

lemma gdc_nc_0876: "gdc_sub None 876"
  by (gdc_eval gdc_nc_0876)

lemma gdc_nc_0877: "gdc_sub None 877"
  by (gdc_eval gdc_nc_0877)

lemma gdc_nc_0878: "gdc_sub None 878"
  by (gdc_eval gdc_nc_0878)

lemma gdc_nc_0879: "gdc_sub None 879"
  by (gdc_eval gdc_nc_0879)

lemma gupt_nc_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma gsec_nc_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding gupt_nc_054 .
  then show "gdc_sub None j" using gdc_nc_0864 gdc_nc_0865 gdc_nc_0866 gdc_nc_0867 gdc_nc_0868 gdc_nc_0869 gdc_nc_0870 gdc_nc_0871 gdc_nc_0872 gdc_nc_0873 gdc_nc_0874 gdc_nc_0875 gdc_nc_0876 gdc_nc_0877 gdc_nc_0878 gdc_nc_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
