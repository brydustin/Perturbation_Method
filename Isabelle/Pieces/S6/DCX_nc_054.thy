theory DCX_nc_054
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0864: "dc_sub None 864"
  by (dc_eval dc_nc_0864)

lemma dc_nc_0865: "dc_sub None 865"
  by (dc_eval dc_nc_0865)

lemma dc_nc_0866: "dc_sub None 866"
  by (dc_eval dc_nc_0866)

lemma dc_nc_0867: "dc_sub None 867"
  by (dc_eval dc_nc_0867)

lemma dc_nc_0868: "dc_sub None 868"
  by (dc_eval dc_nc_0868)

lemma dc_nc_0869: "dc_sub None 869"
  by (dc_eval dc_nc_0869)

lemma dc_nc_0870: "dc_sub None 870"
  by (dc_eval dc_nc_0870)

lemma dc_nc_0871: "dc_sub None 871"
  by (dc_eval dc_nc_0871)

lemma dc_nc_0872: "dc_sub None 872"
  by (dc_eval dc_nc_0872)

lemma dc_nc_0873: "dc_sub None 873"
  by (dc_eval dc_nc_0873)

lemma dc_nc_0874: "dc_sub None 874"
  by (dc_eval dc_nc_0874)

lemma dc_nc_0875: "dc_sub None 875"
  by (dc_eval dc_nc_0875)

lemma dc_nc_0876: "dc_sub None 876"
  by (dc_eval dc_nc_0876)

lemma dc_nc_0877: "dc_sub None 877"
  by (dc_eval dc_nc_0877)

lemma dc_nc_0878: "dc_sub None 878"
  by (dc_eval dc_nc_0878)

lemma dc_nc_0879: "dc_sub None 879"
  by (dc_eval dc_nc_0879)

lemma upt_nc_054: "[864..<880] = [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]"
  by (simp add: upt_rec)

lemma sec_nc_054: "\<forall>j\<in>{16 * 54..<16 * 54 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 54..<16 * 54 + 16}"
  then have "j \<in> set [864..<880]" unfolding set_upt by simp
  then have "j \<in> set [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]" unfolding upt_nc_054 .
  then show "dc_sub None j" using dc_nc_0864 dc_nc_0865 dc_nc_0866 dc_nc_0867 dc_nc_0868 dc_nc_0869 dc_nc_0870 dc_nc_0871 dc_nc_0872 dc_nc_0873 dc_nc_0874 dc_nc_0875 dc_nc_0876 dc_nc_0877 dc_nc_0878 dc_nc_0879
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
