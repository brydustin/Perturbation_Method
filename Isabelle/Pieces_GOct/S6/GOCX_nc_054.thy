theory GOCX_nc_054
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0864: "goc_sub None 864"
  by (goc_eval goc_nc_0864)

lemma goc_nc_0865: "goc_sub None 865"
  by (goc_eval goc_nc_0865)

lemma goc_nc_0866: "goc_sub None 866"
  by (goc_eval goc_nc_0866)

lemma goc_nc_0867: "goc_sub None 867"
  by (goc_eval goc_nc_0867)

lemma goc_nc_0868: "goc_sub None 868"
  by (goc_eval goc_nc_0868)

lemma goc_nc_0869: "goc_sub None 869"
  by (goc_eval goc_nc_0869)

lemma goc_nc_0870: "goc_sub None 870"
  by (goc_eval goc_nc_0870)

lemma goc_nc_0871: "goc_sub None 871"
  by (goc_eval goc_nc_0871)

lemma goc_nc_0872: "goc_sub None 872"
  by (goc_eval goc_nc_0872)

lemma goc_nc_0873: "goc_sub None 873"
  by (goc_eval goc_nc_0873)

lemma goc_nc_0874: "goc_sub None 874"
  by (goc_eval goc_nc_0874)

lemma goc_nc_0875: "goc_sub None 875"
  by (goc_eval goc_nc_0875)

lemma goc_nc_0876: "goc_sub None 876"
  by (goc_eval goc_nc_0876)

lemma goc_nc_0877: "goc_sub None 877"
  by (goc_eval goc_nc_0877)

lemma goc_nc_0878: "goc_sub None 878"
  by (goc_eval goc_nc_0878)

lemma goc_nc_0879: "goc_sub None 879"
  by (goc_eval goc_nc_0879)

lemma gupt_nc_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma gsec_nc_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding gupt_nc_054 .
  then show "goc_sub None j" using goc_nc_0864 goc_nc_0865 goc_nc_0866 goc_nc_0867 goc_nc_0868 goc_nc_0869 goc_nc_0870 goc_nc_0871 goc_nc_0872 goc_nc_0873 goc_nc_0874 goc_nc_0875 goc_nc_0876 goc_nc_0877 goc_nc_0878 goc_nc_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
